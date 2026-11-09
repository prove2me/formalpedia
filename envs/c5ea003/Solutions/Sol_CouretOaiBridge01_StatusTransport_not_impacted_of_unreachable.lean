-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.not_impacted_of_unreachable
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:46:32.665941+00:00
-- url     : https://prove2.me/submissions/5c934c9c-eb01-43da-9866-1cd5cb76d178

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









/--
A node that is unreachable from every changed seed is not impacted.
This is the core "no global invalidation" theorem.
-/
theorem p2m_local_not_impacted_of_unreachable
    {α : Type*} {edge : α → α → Prop} {changed : α → Prop}
    {x : α}
    (h : ∀ s, changed s → ¬ Reach edge s x) :
    ¬ Impacted edge changed x := by
  intro hx
  rcases hx with ⟨s, hs, hsx⟩
  exact h s hs hsx



















end StatusTransport
end CouretOaiBridge01

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} {edge : α → α → Prop} {changed : α → Prop} {x : α},
  (∀ (s : α), changed s → Not (@CouretOaiBridge01.StatusTransport.Reach.{p2m_u_0} α edge s x)) →
    Not (@CouretOaiBridge01.StatusTransport.Impacted.{p2m_u_0} α edge changed x) := @_root_.CouretOaiBridge01.StatusTransport.p2m_local_not_impacted_of_unreachable

