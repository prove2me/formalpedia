-- Prove2me | solution 2 for Geometry.KernelPatterns.bell_eq_sum_stirlingSecond
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:03:09.254375+00:00
-- url     : https://prove2.me/submissions/a173db11-da2e-4e87-a4cd-8b940dc1786d

import Mathlib
import Definitions.Def_Geometry_KernelPatterns_BellRecursion
import Definitions.Def_Geometry_KernelPatterns_BraidFlats
open Finset in
theorem solution (n : ℕ) : Nat.bell n = ∑ k ∈ range (n + 1), Nat.stirlingSecond n k := by
  -- `∑_j C(n,j) S(j,k) = S(n+1,k+1)`
  have hT : ∀ n k : ℕ, ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j k
      = Nat.stirlingSecond (n + 1) (k + 1) := by
    intro n
    induction n with
    | zero =>
      intro k
      cases k with
      | zero => simp [Nat.stirlingSecond]
      | succ k => simp [Nat.stirlingSecond]
    | succ n ih =>
      intro k
      -- Pascal: split off `j = 0` and use `C(n+1, j+1) = C(n, j) + C(n, j+1)`
      have hsplit : ∑ j ∈ range (n + 1 + 1), (n + 1).choose j * Nat.stirlingSecond j k
          = ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j k
            + ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond (j + 1) k := by
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib]
        rw [Finset.sum_range_succ (fun j => n.choose (j + 1) * Nat.stirlingSecond (j + 1) k),
          Nat.choose_succ_self, zero_mul, add_zero]
        rw [Finset.sum_range_succ' (fun j => n.choose j * Nat.stirlingSecond j k)]
        simp only [Nat.choose_zero_right]
        ring
      rw [hsplit, ih k]
      cases k with
      | zero =>
        simp [Nat.stirlingSecond_succ_zero, Nat.stirlingSecond_one_right]
      | succ k =>
        -- Stirling recursion `S(j+1,k+1) = (k+1) S(j,k+1) + S(j,k)`
        have hrec : ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond (j + 1) (k + 1)
            = (k + 1) * ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j (k + 1)
              + ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j k := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Nat.stirlingSecond_succ_succ]
          ring
        rw [hrec, ih (k + 1), ih k, Nat.stirlingSecond_succ_succ (n + 1) (k + 1)]
        ring
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [Nat.stirlingSecond]
    | succ n =>
      rw [Nat.bell_succ, Fin.sum_univ_eq_sum_range (fun i => n.choose i * Nat.bell (n - i)) (n + 1)]
      -- reflect `i ↦ n - i` and use `C(n, n-i) = C(n, i)`
      rw [← Finset.sum_range_reflect]
      have hrefl : ∀ i ∈ range (n + 1), n.choose (n + 1 - 1 - i) * Nat.bell (n - (n + 1 - 1 - i))
          = n.choose i * ∑ k ∈ range (n + 1), Nat.stirlingSecond i k := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [show n + 1 - 1 - i = n - i by omega, Nat.choose_symm (show i ≤ n by omega),
          show n - (n - i) = i by omega, ih i (by omega)]
        congr 1
        -- extend the inner sum to `k ≤ n` (the extra terms vanish)
        apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
        intro k hk hk'
        rw [Finset.mem_range] at hk hk'
        exact Nat.stirlingSecond_eq_zero_of_lt (by omega)
      rw [Finset.sum_congr rfl hrefl]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl fun k _ => hT n k]
      rw [Finset.sum_range_succ' (fun k => Nat.stirlingSecond (n + 1) k), Nat.stirlingSecond_succ_zero,
        add_zero]
