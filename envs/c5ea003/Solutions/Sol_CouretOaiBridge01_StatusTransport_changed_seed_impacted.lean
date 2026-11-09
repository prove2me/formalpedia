-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.changed_seed_impacted
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:02:00.928378+00:00
-- url     : https://prove2.me/submissions/a6df818b-253a-4b0f-82d1-7832db68591e

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





/-- Every changed seed is impacted. -/
theorem p2m_local_changed_seed_impacted
    {α : Type*} {edge : α → α → Prop} {changed : α → Prop}
    {x : α} (hx : changed x) :
    Impacted edge changed x := by
  exact ⟨x, hx, Reach.refl x⟩























end StatusTransport
end CouretOaiBridge01

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} {edge : α → α → Prop} {changed : α → Prop} {x : α},
  changed x → @CouretOaiBridge01.StatusTransport.Impacted.{p2m_u_0} α edge changed x := @_root_.CouretOaiBridge01.StatusTransport.p2m_local_changed_seed_impacted

