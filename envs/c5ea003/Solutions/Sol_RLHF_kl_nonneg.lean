-- Prove2me | solution 1 for RLHF.kl_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:22:02.705133+00:00
-- url     : https://prove2.me/submissions/0ba4ab4f-f522-4d51-afe1-69204688400f

import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
open RLHF Finset in
theorem solution {Ω : Type*} [Fintype Ω] {q p : Ω → ℝ} (hq : IsDist q) (hp : IsPosDist p) :
    0 ≤ klDiv q p := by
  obtain ⟨hqnn, hqsum⟩ := hq
  obtain ⟨hppos, hpsum⟩ := hp
  show (0 : ℝ) ≤ ∑ y, q y * Real.log (q y / p y)
  -- pointwise Gibbs bound: `q log(q/p) ≥ q - p`, from `log x ≤ x - 1`
  have key : ∀ y : Ω, q y - p y ≤ q y * Real.log (q y / p y) := by
    intro y
    rcases eq_or_lt_of_le (hqnn y) with h0 | hpos
    · rw [← h0]
      have hpy := hppos y
      have hz : (0 : ℝ) * Real.log (0 / p y) = 0 := by ring
      rw [hz]
      linarith
    · have hpy := hppos y
      have hratio : 0 < p y / q y := div_pos hpy hpos
      have hlog := Real.log_le_sub_one_of_pos hratio
      have hinv : Real.log (q y / p y) = -Real.log (p y / q y) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      have hmul : q y * Real.log (p y / q y) ≤ q y * (p y / q y - 1) :=
        mul_le_mul_of_nonneg_left hlog hpos.le
      have hcancel : q y * (p y / q y - 1) = p y - q y := by field_simp
      rw [hinv]
      nlinarith [hmul, hcancel]
  calc (0 : ℝ) = (∑ y, q y) - ∑ y, p y := by rw [hqsum, hpsum]; ring
    _ = ∑ y, (q y - p y) := (Finset.sum_sub_distrib _ _).symm
    _ ≤ ∑ y, q y * Real.log (q y / p y) := Finset.sum_le_sum fun y _ => key y
