-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.typed_impacted_of_permitted_edge
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:02:26.804187+00:00
-- url     : https://prove2.me/submissions/8f838840-f354-45e1-906e-3f2226aa95c1

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



























/--
If an edge is present in the list and its kind permits the selected axis,
then it belongs to the induced relation.
-/
theorem typed_edge_in_relation
    {α : Type*}
    {edges : List (TypedEdge α)}
    {axis : ImpactAxis}
    {e : TypedEdge α}
    (he : e ∈ edges)
    (hp : permits axis e.kind = true) :
    TypedRelation edges axis e.source e.target := by
  exact ⟨e, he, rfl, rfl, hp⟩

/--
An impacted source propagates to a target only through an edge whose type
is admitted by the axis policy.
-/
theorem p2m_local_typed_impacted_of_permitted_edge
    {α : Type*}
    {edges : List (TypedEdge α)}
    {axis : ImpactAxis}
    {changes : List (ChangeAt α)}
    {e : TypedEdge α}
    (hs : TypedImpacted edges axis changes e.source)
    (he : e ∈ edges)
    (hp : permits axis e.kind = true) :
    TypedImpacted edges axis changes e.target := by
  exact impacted_of_edge hs (typed_edge_in_relation he hp)



end StatusTransport
end CouretOaiBridge01

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} {edges : List.{p2m_u_0} (CouretOaiBridge01.StatusTransport.TypedEdge.{p2m_u_0} α)}
  {axis : CouretOaiBridge01.StatusTransport.ImpactAxis}
  {changes : List.{p2m_u_0} (CouretOaiBridge01.StatusTransport.ChangeAt.{p2m_u_0} α)}
  {e : CouretOaiBridge01.StatusTransport.TypedEdge.{p2m_u_0} α},
  @CouretOaiBridge01.StatusTransport.TypedImpacted.{p2m_u_0} α edges axis changes
      (@CouretOaiBridge01.StatusTransport.TypedEdge.source.{p2m_u_0} α e) →
    @Membership.mem.{p2m_u_0, p2m_u_0} (CouretOaiBridge01.StatusTransport.TypedEdge.{p2m_u_0} α)
        (List.{p2m_u_0} (CouretOaiBridge01.StatusTransport.TypedEdge.{p2m_u_0} α))
        (@List.instMembership.{p2m_u_0} (CouretOaiBridge01.StatusTransport.TypedEdge.{p2m_u_0} α)) edges e →
      @Eq.{1} Bool
          (CouretOaiBridge01.StatusTransport.permits axis
            (@CouretOaiBridge01.StatusTransport.TypedEdge.kind.{p2m_u_0} α e))
          Bool.true →
        @CouretOaiBridge01.StatusTransport.TypedImpacted.{p2m_u_0} α edges axis changes
          (@CouretOaiBridge01.StatusTransport.TypedEdge.target.{p2m_u_0} α e) := @_root_.CouretOaiBridge01.StatusTransport.p2m_local_typed_impacted_of_permitted_edge

