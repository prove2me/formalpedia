-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.impacted_of_edge
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:44:28.242845+00:00
-- url     : https://prove2.me/submissions/17731c7b-0e1b-4b37-bf82-9743558c182e

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







/-- Impact propagates across one direct dependency edge. -/
theorem p2m_local_impacted_of_edge
    {α : Type*} {edge : α → α → Prop} {changed : α → Prop}
    {a b : α}
    (ha : Impacted edge changed a)
    (hab : edge a b) :
    Impacted edge changed b := by
  rcases ha with ⟨s, hs, hreach⟩
  exact ⟨s, hs, Reach.step hreach hab⟩





















end StatusTransport
end CouretOaiBridge01

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} {edge : α → α → Prop} {changed : α → Prop} {a b : α},
  @CouretOaiBridge01.StatusTransport.Impacted.{p2m_u_0} α edge changed a →
    edge a b → @CouretOaiBridge01.StatusTransport.Impacted.{p2m_u_0} α edge changed b := @_root_.CouretOaiBridge01.StatusTransport.p2m_local_impacted_of_edge

