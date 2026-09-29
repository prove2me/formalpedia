-- Prove2me | solution 1 for PolyaTree.polya_tree_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:55:44.475977+00:00
-- url     : https://prove2.me/submissions/6e723820-5176-4f52-80b5-44f81a19d20d

import Mathlib
import Definitions.Def_Bridges_PolyaTreeRecurrence

open PolyaTree Finset in
theorem solution (a : ℕ → ℚ) (ha1 : a 1 = 1)
    (hFE : ∀ n : ℕ, 1 ≤ n →
      (n : ℚ) * a n =
        a n + ∑ j ∈ Finset.Icc 1 (n - 1), a j * (((n - j : ℕ) : ℚ) * sCoeff a (n - j))) :
    a 1 = 1 ∧ ∀ k : ℕ, 2 ≤ k →
      a k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j) := by
  -- `m · [zᵐ]S = ωₘ`, reindexing the divisor sum by `d ↦ m / d`
  have hω : ∀ m : ℕ, (m : ℚ) * sCoeff a m = omegaSeq a m := by
    intro m
    rw [sCoeff, omegaSeq, Finset.mul_sum, ← Nat.sum_div_divisors m (fun d => (d : ℚ) * a d)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hdvd : i ∣ m := Nat.dvd_of_mem_divisors hi
    have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hi).ne'
    rw [Nat.cast_div hdvd hi0]
    ring
  refine ⟨ha1, fun k hk => ?_⟩
  have h := hFE k (by omega)
  simp only [hω] at h
  have hk1 : ((k : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  rw [one_div, ← div_eq_inv_mul, eq_div_iff hk1]
  linear_combination h
