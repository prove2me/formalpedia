-- Prove2me | solution 1 for mme_ordered_rectangular_MM_support_half_pair_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:01:58.663671+00:00
-- url     : https://prove2.me/submissions/21e74f82-654a-4e56-a411-21bb2fc657eb

import Theorems.Thm_mme_rectangular_MM_support_diagonal_block_matching
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-- Ordered-side rectangular matching keeps the smallest pair product,
up to a fixed factor and the inherited subexponential loss. -/
theorem solution (H V W : ℕ) (hH : 0 < H) (hHV : H ≤ V) (hVW : V ≤ W) :
    ∃ E : Finset (Fin H × Fin V × Fin W),
      Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 → x = y ∧ y = z) ∧
      ((H : ℝ) * (V : ℝ) / 2) *
          Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        (E.card : ℝ) := by
  have hfit : V / H * H ≤ V := Nat.div_mul_le_self V H
  obtain ⟨E, hxy, hyz, hzx, hinduced, hcard⟩ :=
    mme_rectangular_MM_support_diagonal_block_matching
      H (V / H) V W hH hfit (hfit.trans hVW)
  refine ⟨E, hxy, hyz, hzx, hinduced, ?_⟩
  have hdivpos : 0 < V / H := Nat.div_pos hHV hH
  have hfloor : V ≤ 2 * (V / H) * H := by
    have hmul := Nat.le_mul_of_pos_right H hdivpos
    have hmod := Nat.mod_lt V hH
    have hdecomp := Nat.mod_add_div V H
    nlinarith
  have hfloorR : (V : ℝ) ≤ 2 * (V / H : ℕ) * (H : ℝ) := by
    exact_mod_cast hfloor
  have hsize : (H : ℝ) * (V : ℝ) / 2 ≤ (V / H : ℕ) * (H : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hfloorR (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
    nlinarith
  exact (mul_le_mul_of_nonneg_right hsize (le_of_lt (Real.exp_pos _))).trans hcard
