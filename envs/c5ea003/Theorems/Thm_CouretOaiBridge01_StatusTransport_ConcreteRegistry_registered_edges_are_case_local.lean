-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_ConcreteRegistry_registered_edges_are_case_local
-- name    : CouretOaiBridge01.StatusTransport.ConcreteRegistry.registered_edges_are_case_local
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:30:20.031728+00:00
-- url     : https://prove2.me/theorems/6f2aaa31-ac68-4433-b249-6e4401f71da2
-- title:
--   Every registered base edge stays within its case
-- statement:
--   Consider the source registry of sixteen nodes partitioned into four cases: G30, T16, Cayley and OAI seven-eighths. A Boolean walk query W(axis,fuel,source,target) starts with equality at fuel zero and otherwise allows equality or one permitted registered edge followed by a query with one less fuel. For every one of the ten listed edges,
--
--   $$\operatorname{case}(\operatorname{source}(e))=\operatorname{case}(\operatorname{target}(e)).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_07_ConcreteRegistry.lean#L103-L108, lines 103–108; source file SHA-256 f05696e1b6dceb29b803de0750e8abb77295768df7abf264c8b4fef8d5008900; theorem CouretOaiBridge01.StatusTransport.ConcreteRegistry.registered_edges_are_case_local

import Definitions.Def_Couret_STAT_TRANS_07_ConcreteRegistry_d1fd54ec4183
import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_06_AdversarialCases_e73cf4a1e1dc

/-!
# STAT-TRANS-07 — Concrete scientific case registry

This layer replaces the generic A/B/C/D labels by concrete claim identifiers
for the four first scientific case studies.

Artifact ids are metadata only. Lean certifies the graph topology and the
typed propagation policy; it does not authenticate Google Drive or GitHub
contents from a string identifier.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace ConcreteRegistry

theorem registered_edges_are_case_local :
    ∀ edge ∈ concreteEdges, caseOf edge.source = caseOf edge.target := by sorry














end ConcreteRegistry
end StatusTransport
end CouretOaiBridge01
