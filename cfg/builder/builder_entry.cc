#include "ast/Helpers.h"
#include "cfg/builder/builder.h"
#include "common/sort.h"
#include "core/Names.h"

using namespace std;

namespace sorbet::cfg {

unique_ptr<CFG> CFGBuilder::buildFor(core::Context ctx, ast::MethodDef &md) {
    Timer timeit(ctx.state.tracer(), "cfg");
    ENFORCE(md.symbol.exists());
    ENFORCE(!md.symbol.data(ctx)->isOverloaded());
    unique_ptr<CFG> res(new CFG); // private constructor
    res->file = md.declLoc.file();
    res->symbol = md.symbol.data(ctx)->dealiasMethod(ctx);
    u4 temporaryCounter = 1;
    UnorderedMap<core::SymbolRef, LocalRef> aliases;
    UnorderedMap<core::NameRef, LocalRef> discoveredUndeclaredFields;
    CFGContext cctx(ctx, *res.get(), LocalRef::noVariable(), 0, nullptr, nullptr, nullptr, aliases,
                    discoveredUndeclaredFields, temporaryCounter);

    LocalRef retSym;
    BasicBlock *entry = res->entry();
    BasicBlock *cont;
    {
        CFG::UnfreezeCFGLocalVariables unfreezeVars(*res);
        retSym = cctx.newTemporary(core::Names::returnMethodTemp());

        auto selfClaz = md.symbol.data(ctx)->rebind();
        if (!selfClaz.exists()) {
            selfClaz = md.symbol;
        }
        synthesizeExpr(entry, LocalRef::selfVariable(), md.loc,
                       make_unique<Cast>(LocalRef::selfVariable(),
                                         selfClaz.data(ctx)->enclosingClass(ctx).data(ctx)->selfType(ctx),
                                         core::Names::cast()));

        BasicBlock *presentCont = entry;
        BasicBlock *defaultCont = nullptr;

        auto &argInfos = md.symbol.data(ctx)->arguments();
        int i = -1;
        for (auto &argExpr : md.args) {
            i++;
            auto *a = ast::MK::arg2Local(argExpr);
            auto local = res->enterLocal(a->localVariable);
            auto &info = argInfos[i];

            // If this is a keyword argument, we can no longer make the assumption that processing one default arg
            // means the remaining will all be defaulted; join together the present and defaulted branches, to force
            // explicit checks for all remaining keyword arguments.
            if (info.flags.isKeyword && nullptr != defaultCont) {
                auto *join = res->freshBlock(cctx.loops, presentCont->rubyBlockId);
                unconditionalJump(presentCont, join, *res, core::LocOffsets::none());
                unconditionalJump(defaultCont, join, *res, core::LocOffsets::none());
                presentCont = join;
                defaultCont = nullptr;
            }

            // Only emit conditional arg loading if the arg has a default
            if (auto *opt = ast::cast_tree<ast::OptionalArg>(argExpr)) {
                auto defLoc = opt->default_->loc;

                auto *presentNext = res->freshBlock(cctx.loops, presentCont->rubyBlockId);
                auto *defaultNext = res->freshBlock(cctx.loops, presentCont->rubyBlockId);

                auto present = cctx.newTemporary(core::Names::argPresent());
                synthesizeExpr(presentCont, present, a->loc, make_unique<ArgPresent>(md.symbol, i));
                conditionalJump(presentCont, present, presentNext, defaultNext, *res, a->loc);

                if (defaultCont) {
                    unconditionalJump(defaultCont, defaultNext, *res, a->loc);
                }

                // Walk the default, and check the type of its final value
                auto result = cctx.newTemporary(core::Names::statTemp());
                defaultNext = walk(cctx.withTarget(result), *opt->default_, defaultNext);

                if (info.type) {
                    auto tmp = cctx.newTemporary(core::Names::castTemp());
                    defaultNext->exprs.emplace_back(tmp, defLoc,
                                                    make_unique<Cast>(result, info.type, core::Names::let()));
                    result = tmp;
                }

                defaultNext->exprs.emplace_back(local, defLoc, make_unique<Ident>(result));

                presentCont = presentNext;
                defaultCont = defaultNext;
            }

            synthesizeExpr(presentCont, local, a->loc, make_unique<LoadArg>(md.symbol, i));
        }

        // Join the presentCont and defaultCont paths together
        if (defaultCont) {
            auto *join = res->freshBlock(cctx.loops, presentCont->rubyBlockId);
            unconditionalJump(presentCont, join, *res, core::LocOffsets::none());
            unconditionalJump(defaultCont, join, *res, core::LocOffsets::none());
            presentCont = join;
        }

        cont = walk(cctx.withTarget(retSym), md.rhs.get(), presentCont);
    }
    // Past this point, res->localVariables is a fixed size.

    LocalRef retSym1 = LocalRef::finalReturn();

    auto rvLoc = cont->exprs.empty() || isa_instruction<LoadArg>(cont->exprs.back().value.get())
                     ? md.loc
                     : cont->exprs.back().loc;
    synthesizeExpr(cont, retSym1, rvLoc, make_unique<Return>(retSym)); // dead assign.
    jumpToDead(cont, *res.get(), rvLoc);

    vector<Binding> aliasesPrefix;
    for (auto kv : aliases) {
        core::SymbolRef global = kv.first;
        LocalRef local = kv.second;
        aliasesPrefix.emplace_back(local, core::LocOffsets::none(), make_unique<Alias>(global));
        if (global.data(ctx)->isField() || global.data(ctx)->isStaticField()) {
            res->minLoops[local.id()] = CFG::MIN_LOOP_FIELD;
        } else {
            res->minLoops[local.id()] = CFG::MIN_LOOP_GLOBAL;
        }
    }
    for (auto kv : discoveredUndeclaredFields) {
        aliasesPrefix.emplace_back(kv.second, core::LocOffsets::none(),
                                   make_unique<Alias>(core::Symbols::Magic_undeclaredFieldStub(), kv.first));
        res->minLoops[kv.second.id()] = CFG::MIN_LOOP_FIELD;
    }
    histogramInc("cfgbuilder.aliases", aliasesPrefix.size());
    auto basicBlockCreated = res->basicBlocks.size();
    histogramInc("cfgbuilder.basicBlocksCreated", basicBlockCreated);
    fast_sort(aliasesPrefix,
              [](const Binding &l, const Binding &r) -> bool { return l.bind.variable.id() < r.bind.variable.id(); });

    entry->exprs.insert(entry->exprs.begin(), make_move_iterator(aliasesPrefix.begin()),
                        make_move_iterator(aliasesPrefix.end()));
    res->sanityCheck(ctx);
    sanityCheck(ctx, *res);
    fillInTopoSorts(ctx, *res);
    dealias(ctx, *res);
    CFG::ReadsAndWrites RnW = res->findAllReadsAndWrites(ctx);
    computeMinMaxLoops(ctx, RnW, *res);
    fillInBlockArguments(ctx, RnW, *res);
    removeDeadAssigns(ctx, RnW, *res); // requires block arguments to be filled
    simplify(ctx, *res);
    histogramInc("cfgbuilder.basicBlocksSimplified", basicBlockCreated - res->basicBlocks.size());
    markLoopHeaders(ctx, *res);
    sanityCheck(ctx, *res);
    res->sanityCheck(ctx);
    histogramInc("cfgbuilder.numLocalVariables", res->numLocalVariables());
    return res;
}

void CFGBuilder::fillInTopoSorts(core::Context ctx, CFG &cfg) {
    auto &target1 = cfg.forwardsTopoSort;
    target1.resize(cfg.basicBlocks.size());
    int count = topoSortFwd(target1, 0, cfg.entry());
    cfg.forwardsTopoSort.resize(count);

    // Remove unreachable blocks (which were not found by the toposort)
    for (auto &bb : cfg.basicBlocks) {
        if (bb->fwdId == -1) {
            for (auto &prev : bb->backEdges) {
                ENFORCE(prev->fwdId == -1);
            }

            bb->bexit.thenb->backEdges.erase(
                remove(bb->bexit.thenb->backEdges.begin(), bb->bexit.thenb->backEdges.end(), bb.get()),
                bb->bexit.thenb->backEdges.end());
            bb->bexit.elseb->backEdges.erase(
                remove(bb->bexit.elseb->backEdges.begin(), bb->bexit.elseb->backEdges.end(), bb.get()),
                bb->bexit.elseb->backEdges.end());
        }
    }
    cfg.basicBlocks.erase(
        remove_if(cfg.basicBlocks.begin(), cfg.basicBlocks.end(), [](auto &bb) -> bool { return bb->fwdId == -1; }),
        cfg.basicBlocks.end());

    // needed to find loop headers.
    for (auto &bb : cfg.basicBlocks) {
        fast_sort(bb->backEdges, [](const BasicBlock *a, const BasicBlock *b) -> bool { return a->fwdId > b->fwdId; });
    }
}

CFGContext CFGContext::withTarget(LocalRef target) {
    auto ret = CFGContext(*this);
    ret.target = target;
    return ret;
}

CFGContext CFGContext::withBlockBreakTarget(LocalRef blockBreakTarget) {
    auto ret = CFGContext(*this);
    ret.blockBreakTarget = blockBreakTarget;
    return ret;
}

CFGContext CFGContext::withLoopScope(BasicBlock *nextScope, BasicBlock *breakScope, bool insideRubyBlock) {
    auto ret = CFGContext(*this);
    ret.nextScope = nextScope;
    ret.breakScope = breakScope;
    ret.isInsideRubyBlock = insideRubyBlock;
    ret.loops += 1;
    return ret;
}

CFGContext CFGContext::withSendAndBlockLink(const shared_ptr<core::SendAndBlockLink> &link) {
    auto ret = CFGContext(*this);
    ret.link = link;
    return ret;
}

} // namespace sorbet::cfg
