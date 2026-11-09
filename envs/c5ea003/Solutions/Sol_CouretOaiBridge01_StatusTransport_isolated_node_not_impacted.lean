-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.isolated_node_not_impacted
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:01:46.165678+00:00
-- url     : https://prove2.me/submissions/840332a0-7c67-4f65-a9d7-f9e3c8a7ab91

import Definitions.Def_Couret_STAT_TRANS_03_DependencyGraph_a12904c0d89d
import Mathlib.Data.Set.Basic
import Theorems.Thm_CouretOaiBridge01_StatusTransport_not_impacted_of_unreachable
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
A dependency-free node distinct from all changed seeds is not impacted.
This makes explicit that isolated claims survive unrelated changes.
-/
theorem p2m_local_isolated_node_not_impacted
    {α : Type*} {edge : α → α → Prop} {changed : α → Prop}
    {x : α}
    (hseed : ¬ changed x)
    (hin : ∀ y, ¬ edge y x) :
    ¬ Impacted edge changed x := by
  apply not_impacted_of_unreachable
  intro s hs hreach
  cases hreach with
  | refl =>
      exact hseed hs
  | step _ hlast =>
      exact hin _ hlast















end StatusTransport
end CouretOaiBridge01

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} {edge : α → α → Prop} {changed : α → Prop} {x : α},
  Not (changed x) →
    (∀ (y : α), Not (edge y x)) → Not (@CouretOaiBridge01.StatusTransport.Impacted.{p2m_u_0} α edge changed x) := @_root_.CouretOaiBridge01.StatusTransport.p2m_local_isolated_node_not_impacted

