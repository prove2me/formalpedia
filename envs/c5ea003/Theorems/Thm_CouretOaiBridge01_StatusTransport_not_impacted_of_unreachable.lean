-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_not_impacted_of_unreachable
-- name    : CouretOaiBridge01.StatusTransport.not_impacted_of_unreachable
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:46:27.852698+00:00
-- url     : https://prove2.me/theorems/97fa85ce-94a4-4c72-87c2-151906c4c275
-- title:
--   Unreachable nodes are not impacted
-- statement:
--   For any edge relation, changed seeds and node $x$, if no changed seed reaches $x$, then $x$ is not impacted.
--
--   Reachability includes paths of length zero.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_03_DependencyGraph.lean#L50-L61, lines 50–61; source file SHA-256 4e4de934f82aabd60e1dbb0a688ba35489f034249c2859a3a500801ac79d1b30; theorem CouretOaiBridge01.StatusTransport.not_impacted_of_unreachable

import Definitions.Def_Couret_STAT_TRANS_03_DependencyGraph_a12904c0d89d
import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_02_ClaimContract_997da1c8f8df

/-!
# STAT-TRANS-03 — Dependency graph and differential invalidation

This file formalizes a minimal dependency graph for claim-contract invalidation.

Orientation:
  edge a b
means:
  b directly depends on a.

A change at a node propagates only to nodes reachable from that node.
The construction is deliberately generic and does not encode a global
"everything invalidates everything" policy.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport

theorem not_impacted_of_unreachable
    {α : Type*} {edge : α → α → Prop} {changed : α → Prop}
    {x : α}
    (h : ∀ s, changed s → ¬ Reach edge s x) :
    ¬ Impacted edge changed x := by sorry




















end StatusTransport
end CouretOaiBridge01
