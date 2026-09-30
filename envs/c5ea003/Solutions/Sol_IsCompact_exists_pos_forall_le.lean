-- Prove2me | solution 1 for IsCompact.exists_pos_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-29T22:43:02.939989+00:00
-- url     : https://prove2.me/submissions/a8f128e1-8c77-4b10-8f3b-fae9c34f2ce4

import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real

set_option autoImplicit false

open IsCompact

theorem solution {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsCompact s) (hne : s.Nonempty) {f : X → ℝ}
    (hf : ContinuousOn f s) (hpos : ∀ x ∈ s, 0 < f x) :
    ∃ m > 0, ∀ x ∈ s, m ≤ f x := by
  obtain ⟨x, hx, hxmin⟩ := hs.exists_isMinOn hne hf
  exact ⟨f x, hpos x hx, fun y hy ↦ hxmin hy⟩
