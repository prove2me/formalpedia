-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_typed_impacted_of_permitted_edge
-- name    : CouretOaiBridge01.StatusTransport.typed_impacted_of_permitted_edge
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:02:21.34345+00:00
-- url     : https://prove2.me/theorems/dae6bf50-362a-46f3-a456-a366723fcda5
-- title:
--   A permitted registered dependency propagates impact
-- statement:
--   For any node type, typed-edge list, impact axis and list of changes, let $e$ be an edge in the list whose kind permits the axis. If its source is impacted under axis-filtered reachability from the corresponding changed seeds, then its target is impacted.
--
--   The impact axis remains fixed throughout the step.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_04_TypedDependencies.lean#L124-L138, lines 124–138; source file SHA-256 281beb127656947f4f40697a7241993ba3e4cf18764a18bef5cb9ba1952cd375; theorem CouretOaiBridge01.StatusTransport.typed_impacted_of_permitted_edge

import Definitions.Def_Couret_STAT_TRANS_04_TypedDependencies_3df632007942
import Mathlib.Data.Set.Basic
import Theorems.Thm_CouretOaiBridge01_StatusTransport_impacted_of_edge
import Definitions.Def_Couret_STAT_TRANS_03_DependencyGraph_a12904c0d89d

/-!
# STAT-TRANS-04 — Typed dependencies

This layer distinguishes dependency kinds so that invalidation propagates
only along edges relevant to the affected axis.

No global scalar status is introduced.
No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport

theorem typed_impacted_of_permitted_edge
    {α : Type*}
    {edges : List (TypedEdge α)}
    {axis : ImpactAxis}
    {changes : List (ChangeAt α)}
    {e : TypedEdge α}
    (hs : TypedImpacted edges axis changes e.source)
    (he : e ∈ edges)
    (hp : permits axis e.kind = true) :
    TypedImpacted edges axis changes e.target := by sorry




end StatusTransport
end CouretOaiBridge01
