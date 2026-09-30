-- Prove2me | solution 1 for HirschCircuit.exists_positive_maximal_nonnegative_step
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-08T18:50:33.946517+00:00
-- url     : https://prove2.me/submissions/f50c9365-64d5-41ef-95fb-34c3e4ed8653

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Direct proof of existence of a strictly positive maximal nonnegative step. -/
theorem solution {n : ℕ}
    (x g : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hzero : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ α : ℝ, 0 < α ∧ (∀ i, 0 ≤ x i + α * g i) ∧
      (∃ q, g q < 0 ∧ x q + α * g q = 0) ∧
      ∀ β : ℝ, α < β → ∃ i, x i + β * g i < 0 := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter (fun i => g i < 0)
  have hD : D.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simp [D, hi]⟩
  obtain ⟨q, hqD, hmin⟩ := D.exists_min_image (fun i => x i / (-g i)) hD
  have hq : g q < 0 := (Finset.mem_filter.mp hqD).2
  have hxq : 0 < x q := by
    have hn := hx q
    by_contra hh
    have hz : x q = 0 := le_antisymm (le_of_not_gt hh) hn
    have := hzero q hz
    linarith
  let α : ℝ := x q / (-g q)
  have hα : 0 < α := div_pos hxq (neg_pos.mpr hq)
  have hsat : x q + α * g q = 0 := by
    have he : α * (-g q) = x q := div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hq))
    nlinarith
  refine ⟨α, hα, ?_, ⟨q, hq, hsat⟩, ?_⟩
  · intro i
    by_cases hi : g i < 0
    · have hle : α ≤ x i / (-g i) := hmin i (by simp [D, hi])
      have hmul := (le_div_iff₀ (neg_pos.mpr hi)).mp hle
      nlinarith
    · exact add_nonneg (hx i) (mul_nonneg (le_of_lt hα) (le_of_not_gt hi))
  · intro β hβ
    refine ⟨q, ?_⟩
    have := mul_lt_mul_of_pos_right hβ (neg_pos.mpr hq)
    nlinarith

#print axioms solution
