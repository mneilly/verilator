// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Order's Transformations:
//
//  Compute near optimal scheduling of always/wire statements
//  Make a graph of the entire netlist
//
//      For seq logic
//          Add logic_sensitive_vertex for this list of SenItems
//              Add edge for each sensitive_var->logic_sensitive_vertex
//          For AlwaysPre's
//              Add vertex for this logic
//                  Add edge logic_sensitive_vertex->logic_vertex
//                  Add edge logic_consumed_var_PREVAR->logic_vertex
//                  Add edge logic_vertex->logic_generated_var (same as if comb)
//                  Add edge logic_vertex->generated_var_PREORDER
//                      Cutable dependency to attempt to order dlyed
//                      assignments to avoid saving state, thus we prefer
//                              a <= b ...      As the opposite order would
//                              b <= c ...      require the old value of b.
//                  Add edge consumed_var_POST->logic_vertex
//                      This prevents a consumer of the "early" value to be
//                      scheduled after we've changed to the next-cycle value
//          For Logic
//              Add vertex for this logic
//                  Add edge logic_sensitive_vertex->logic_vertex
//                  Add edge logic_generated_var_PREORDER->logic_vertex
//                      This ensures the AlwaysPre gets scheduled before this logic
//                  Add edge logic_vertex->consumed_var_PREVAR
//                  Add edge logic_vertex->consumed_var_POSTVAR
//                  Add edge logic_vertex->logic_generated_var (same as if comb)
//          For AlwaysPost's
//              Add vertex for this logic
//                  Add edge logic_sensitive_vertex->logic_vertex
//                  Add edge logic_consumed_var->logic_vertex (same as if comb)
//                  Add edge logic_vertex->logic_generated_var (same as if comb)
//                  Add edge consumed_var_POST->logic_vertex (same as if comb)
//
//      For comb logic
//          For comb logic
//              Add vertex for this logic
//              Add edge logic_consumed_var->logic_vertex
//              Add edge logic_vertex->logic_generated_var
//                  Mark it cutable, as circular logic may require
//                  the generated signal to become a primary input again.
//
//
//
//   Rank the graph starting at INPUTS (see V3Graph)
//
//   Visit the graph's logic vertices in ranked order
//      For all logic vertices with all inputs already ordered
//         Make ordered block for this module
//         For all ^^ in same domain
//              Move logic to ordered activation
//      When we have no more choices, we move to the next module
//      and make a new block.  Add that new activation block to the list of calls to make.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3OrderInternal.h"
#include "V3Sched.h"

#include <memory>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

//######################################################################
// Struct field usage analysis

class StructFieldAnalyzer final : public VNVisitor {
    // Analyze which struct fields are read/written in combinational logic
    V3Sched::StructFieldUsage* m_currentUsage = nullptr;
    AstNodeDType* m_currentStructDtp = nullptr;
    bool m_inLValue = false;

    // Get bit position for a field in a struct (max 64 fields supported)
    uint32_t getFieldBitPosition(const AstNodeUOrStructDType* structDtp, const std::string& fieldName) {
        uint32_t bitPos = 0;
        for (const AstMemberDType* memberp = structDtp->membersp(); memberp;
             memberp = VN_AS(memberp->nextp(), MemberDType)) {
            if (memberp->name() == fieldName) return bitPos;
            bitPos++;
            if (bitPos >= 64) {
                // Struct has more than 64 fields - diagnostics will only track first 64
                return 63;  // Cap at 63
            }
        }
        return 0;
    }

    // Get all field names from a struct
    void extractFieldNames(const AstNodeUOrStructDType* structDtp,
                          std::vector<std::string>& fieldNames) {
        for (const AstMemberDType* memberp = structDtp->membersp(); memberp;
             memberp = VN_AS(memberp->nextp(), MemberDType)) {
            if (fieldNames.size() >= 64) break;
            fieldNames.push_back(memberp->name());
        }
    }

    void visit(AstNodeVarRef* nodep) override {
        // Check if this is a struct variable reference
        AstNodeDType* const dtypep = nodep->varp()->dtypep()->skipRefp();
        if (const AstNodeUOrStructDType* const structDtp = VN_CAST(dtypep, NodeUOrStructDType)) {
            // Whole struct referenced - mark all fields as used
            auto& usage = V3Sched::g_structFieldUsage[nodep->varScopep()];
            if (usage.structVscp == nullptr) {
                usage.structVscp = nodep->varScopep();
                extractFieldNames(structDtp, usage.fieldNames);
            }
            // Mark all fields as read or written
            const uint64_t allFields = (1ULL << usage.fieldNames.size()) - 1;
            if (nodep->access().isWriteOrRW()) {
                usage.fieldsWritten |= allFields;
            } else {
                usage.fieldsRead |= allFields;
            }
        }
    }

    void visit(AstMemberSel* nodep) override {
        // Track individual field access
        AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefp();
        if (const AstNodeUOrStructDType* const structDtp = VN_CAST(fromDtp, NodeUOrStructDType)) {
            // Get the base variable
            if (AstVarRef* const varrefp = VN_CAST(nodep->fromp(), VarRef)) {
                auto& usage = V3Sched::g_structFieldUsage[varrefp->varScopep()];
                if (usage.structVscp == nullptr) {
                    usage.structVscp = varrefp->varScopep();
                    extractFieldNames(structDtp, usage.fieldNames);
                }
                
                const uint32_t fieldBit = getFieldBitPosition(structDtp, nodep->name());
                const uint64_t fieldMask = 1ULL << fieldBit;
                
                if (nodep->access().isWriteOrRW()) {
                    usage.fieldsWritten |= fieldMask;
                } else {
                    usage.fieldsRead |= fieldMask;
                }
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override {
        iterateChildren(nodep);
    }

public:
    explicit StructFieldAnalyzer(AstNode* nodep) {
        iterate(nodep);
    }
    ~StructFieldAnalyzer() = default;
};

}  // namespace

void V3Order::orderOrderGraph(OrderGraph& graph, const std::string& tag) {
    // Dump data
    if (dumpGraphLevel()) graph.dumpDotFilePrefixed(tag + "_orderg_pre");

    // Break cycles. Note that the OrderGraph only contains cuttable cycles
    // (soft constraints). Actual logic loops must have been eliminated by
    // the introduction of Hybid sensitivity expressions, before invoking
    // ordering (e.g. in V3SchedAcyclic).
    graph.acyclic(&V3GraphEdge::followAlwaysTrue);
    if (dumpGraphLevel()) graph.dumpDotFilePrefixed(tag + "_orderg_acyc");

    // Assign ranks so we know what to follow, then sort vertices and edges by that ordering
    graph.order();
    if (dumpGraphLevel()) graph.dumpDotFilePrefixed(tag + "_orderg_order");
}

//######################################################################

AstCFunc* V3Order::order(AstNetlist* netlistp,  //
                         const std::vector<V3Sched::LogicByScope*>& logic,  //
                         const V3Order::TrigToSenMap& trigToSen,
                         const string& tag,  //
                         bool parallel,  //
                         bool slow,  //
                         const ExternalDomainsProvider& externalDomains) {
    // Build the OrderGraph
    const std::unique_ptr<OrderGraph> graph = buildOrderGraph(netlistp, logic, trigToSen);
    
    // Analyze struct field usage for runtime diagnostics (VL_DEBUG only)
    for (auto* const lbsp : logic) {
        lbsp->foreachLogic([](AstNode* logicp) {
            StructFieldAnalyzer{logicp};
        });
    }
    
    // Order it
    orderOrderGraph(*graph, tag);
    // Assign sensitivity domains to combinational logic
    processDomains(netlistp, *graph, tag, externalDomains);
    // Build the move graph
    OrderMoveDomScope::clear();
    const std::unique_ptr<OrderMoveGraph> moveGraphp = OrderMoveGraph::build(*graph, trigToSen);
    if (dumpGraphLevel() >= 9) moveGraphp->dumpDotFilePrefixed(tag + "_ordermv");

    // The ordered statements, if there are any
    AstNodeStmt* stmtsp = nullptr;
    if (!moveGraphp->empty()) {
        if (parallel) {
            stmtsp = createParallel(*graph, *moveGraphp, tag, slow);
        } else {
            stmtsp = createSerial(*moveGraphp, tag, slow);
        }
        // Should have consumed all vertices
        UASSERT(moveGraphp->empty(), "Unconsumed vertices remain in OrderMoveGraph");
    }
    OrderMoveDomScope::clear();

    // Dump data
    if (dumpGraphLevel()) graph->dumpDotFilePrefixed(tag + "_orderg_done");

    // Dispose of the remnants of the inputs
    for (auto* const lbsp : logic) lbsp->deleteActives();

    // If there is no resulting logic, then don't create an empty function
    if (!stmtsp) return nullptr;

    // Create the result function
    FileLine* const flp = netlistp->fileline();
    AstCFunc* const funcp = [&]() {
        AstScope* const scopeTopp = netlistp->topScopep()->scopep();
        AstCFunc* const resp = new AstCFunc{flp, "_eval_" + tag, scopeTopp, ""};
        resp->dontCombine(true);
        resp->isStatic(false);
        resp->isLoose(true);
        resp->slow(slow);
        resp->isConst(false);
        resp->declPrivate(true);
        scopeTopp->addBlocksp(resp);
        return resp;
    }();

    // Assemble the body
    if (v3Global.opt.profExec()) {
        funcp->addStmtsp(AstCStmt::profExecSectionPush(flp, "func " + tag));
    }
    funcp->addStmtsp(stmtsp);
    if (v3Global.opt.profExec()) {  //
        funcp->addStmtsp(AstCStmt::profExecSectionPop(flp, "func " + tag));
    }

    // Done
    return funcp;
}
