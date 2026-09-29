-- Prove2me | solution 1 for mme_dwz_aggregate_group_count_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:30:06.297537+00:00
-- url     : https://prove2.me/submissions/9b119114-21cb-4b56-8e55-d8995b1d2bb5

import Mathlib

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (t : ℕ) (ht : 0 < t) (A total : ℝ)
    (hlarge : 16 * (t : ℝ) ≤ A) (hAtotal : A ≤ total) :
    ∃ q : ℕ,
      A / (16 * (t : ℝ)) ≤ (q : ℝ) ∧
      (q : ℝ) * ((t : ℝ) + 1) ≤ total := by
  let x : ℝ := A / (16 * (t : ℝ))
  let q : ℕ := ⌈x⌉₊
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hdenom : (0 : ℝ) < 16 * (t : ℝ) := by positivity
  have hA : 0 ≤ A := le_trans (by positivity) hlarge
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hxOne : 1 ≤ x := by
    dsimp only [x]
    exact (le_div_iff₀ hdenom).2 (by simpa [mul_comm] using hlarge)
  have hxDenom : x * (16 * (t : ℝ)) = A := by
    dsimp only [x]
    field_simp
  have hqLower : x ≤ (q : ℝ) := by
    dsimp only [q]
    exact Nat.le_ceil x
  have hqUpper : (q : ℝ) < x + 1 := by
    dsimp only [q]
    exact Nat.ceil_lt_add_one hx
  have hproduct :
      (x + 1) * ((t : ℝ) + 1) ≤ A := by
    have hcross : 0 ≤ (x - 1) * ((t : ℝ) - 1) :=
      mul_nonneg (sub_nonneg.mpr hxOne) (sub_nonneg.mpr htR)
    nlinarith
  refine ⟨q, ?_, ?_⟩
  · simpa only [x] using hqLower
  · apply le_trans ?_ hAtotal
    exact (mul_le_mul_of_nonneg_right (le_of_lt hqUpper) (by positivity)).trans
      hproduct

