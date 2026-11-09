-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.not_typed_impacted_of_unreachable
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:01:57.501341+00:00
-- url     : https://prove2.me/submissions/34e5ca9b-0253-4c79-8552-9114b4e6c50c

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































/--
Unreachability in the axis-filtered dependency relation prevents impact.
-/
theorem p2m_local_not_typed_impacted_of_unreachable
    {α : Type*}
    {edges : List (TypedEdge α)}
    {axis : ImpactAxis}
    {changes : List (ChangeAt α)}
    {x : α}
    (h : ∀ s, SeedFor axis changes s →
      ¬ Reach (TypedRelation edges axis) s x) :
    ¬ TypedImpacted edges axis changes x := by
  exact not_impacted_of_unreachable h

end StatusTransport
end CouretOaiBridge01

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} {edges : List.{p2m_u_0} (CouretOaiBridge01.StatusTransport.TypedEdge.{p2m_u_0} α)}
  {axis : CouretOaiBridge01.StatusTransport.ImpactAxis}
  {changes : List.{p2m_u_0} (CouretOaiBridge01.StatusTransport.ChangeAt.{p2m_u_0} α)} {x : α},
  (∀ (s : α),
      @CouretOaiBridge01.StatusTransport.SeedFor.{p2m_u_0} α axis changes s →
        Not
          (@CouretOaiBridge01.StatusTransport.Reach.{p2m_u_0} α
            (@CouretOaiBridge01.StatusTransport.TypedRelation.{p2m_u_0} α edges axis) s x)) →
    Not (@CouretOaiBridge01.StatusTransport.TypedImpacted.{p2m_u_0} α edges axis changes x) := @_root_.CouretOaiBridge01.StatusTransport.p2m_local_not_typed_impacted_of_unreachable

