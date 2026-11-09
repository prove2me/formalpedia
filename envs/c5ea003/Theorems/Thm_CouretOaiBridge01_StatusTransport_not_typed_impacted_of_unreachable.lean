-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_not_typed_impacted_of_unreachable
-- name    : CouretOaiBridge01.StatusTransport.not_typed_impacted_of_unreachable
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:01:53.575666+00:00
-- url     : https://prove2.me/theorems/d356165e-ef4e-4156-bb98-2e43e5fafab3
-- title:
--   Filtered unreachability prevents typed impact
-- statement:
--   For any node type, typed-edge list, axis, changes and node $x$, if no seed of that axis reaches $x$ in the axis-filtered dependency relation, then $x$ is not typed-impacted.
--
--   Reachability is reflexive/transitive.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_04_TypedDependencies.lean#L140-L152, lines 140–152; source file SHA-256 281beb127656947f4f40697a7241993ba3e4cf18764a18bef5cb9ba1952cd375; theorem CouretOaiBridge01.StatusTransport.not_typed_impacted_of_unreachable

import Definitions.Def_Couret_STAT_TRANS_04_TypedDependencies_3df632007942
import Mathlib.Data.Set.Basic
import Theorems.Thm_CouretOaiBridge01_StatusTransport_not_impacted_of_unreachable
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

theorem not_typed_impacted_of_unreachable
    {α : Type*}
    {edges : List (TypedEdge α)}
    {axis : ImpactAxis}
    {changes : List (ChangeAt α)}
    {x : α}
    (h : ∀ s, SeedFor axis changes s →
      ¬ Reach (TypedRelation edges axis) s x) :
    ¬ TypedImpacted edges axis changes x := by sorry


end StatusTransport
end CouretOaiBridge01
