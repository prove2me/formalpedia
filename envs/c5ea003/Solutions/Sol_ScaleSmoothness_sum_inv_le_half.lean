-- Prove2me | solution 1 for ScaleSmoothness.sum_inv_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:42:04.26352+00:00
-- url     : https://prove2.me/submissions/8aeb26f4-1052-4a2e-9af4-d4f05da574ec

import Mathlib
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
open ScaleSmoothness Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 3 ≤ n) :
    ∑ n ∈ S, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) ≤ 1 / 2 := by
  -- partial fractions: `1/(n(n-1)) = 1/(n-1) - 1/n`, the source of the telescoping
  have hsplit : ∀ x : ℚ, x + 2 ≠ 0 → x + 3 ≠ 0 →
      1 / ((x + 3) * ((x + 3) - 1)) = 1 / (x + 2) - 1 / (x + 3) := by
    intro x h2 h3
    rw [show x + 3 - 1 = x + 2 by ring, div_sub_div _ _ h2 h3,
      show 1 * (x + 3) - (x + 2) * 1 = 1 by ring, mul_comm (x + 2) (x + 3)]
  -- the telescoping identity `∑_{n=3}^{m+2} 1/(n(n-1)) = 1/2 - 1/(m+2)`
  have key : ∀ m : ℕ, ∑ n ∈ Finset.Icc 3 (m + 2), (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))
      = 1 / 2 - 1 / ((m : ℚ) + 2) := by
    intro m
    induction m with
    | zero =>
      rw [Finset.Icc_eq_empty (by omega)]
      norm_num
    | succ k ih =>
      have h2 : (k : ℚ) + 2 ≠ 0 := by positivity
      have h3 : (k : ℚ) + 3 ≠ 0 := by positivity
      have hc : ((k + 2 + 1 : ℕ) : ℚ) = (k : ℚ) + 3 := by push_cast; ring
      have hc2 : ((k + 1 : ℕ) : ℚ) + 2 = (k : ℚ) + 3 := by push_cast; ring
      rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.sum_Icc_succ_top (by omega), ih,
        hc, hsplit (k : ℚ) h2 h3, hc2]
      ring
  -- every element of `S` lies in `Icc 3 (sup S + 2)`
  set m := S.sup id with hm
  have hsub : S ⊆ Finset.Icc 3 (m + 2) := by
    intro n hn
    simp only [Finset.mem_Icc]
    refine ⟨hS n hn, ?_⟩
    have := Finset.le_sup (f := id) hn
    simp only [id] at this
    omega
  have hnn : ∀ n ∈ Finset.Icc 3 (m + 2), n ∉ S → (0 : ℚ) ≤ 1 / ((n : ℚ) * ((n : ℚ) - 1)) := by
    intro n hn _
    simp only [Finset.mem_Icc] at hn
    have h3 : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn.1
    apply div_nonneg zero_le_one
    nlinarith
  calc ∑ n ∈ S, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))
      ≤ ∑ n ∈ Finset.Icc 3 (m + 2), (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    _ = 1 / 2 - 1 / ((m : ℚ) + 2) := key m
    _ ≤ 1 / 2 := by
        have hpos : (0 : ℚ) < (m : ℚ) + 2 := by positivity
        have := one_div_pos.mpr hpos
        linarith
