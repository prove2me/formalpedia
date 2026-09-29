-- Prove2me | solution 1 for CausalIntegration.integrate_two_eq_weighted
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:43:28.639767+00:00
-- url     : https://prove2.me/submissions/f8b26f34-ae3f-470e-afa2-ed297e5eabcb

-- Sol generated from Combinatorics/CausalintegrationComposition/CausalIntegration_Composition.lean
import Mathlib
import Definitions.Def_Combinatorics_CausalintegrationComposition_CausalIntegration_Composition
import Definitions.Def_Combinatorics_CausalintegrationCore_CausalIntegration_Core
import Theorems.Thm_CausalIntegration_integrate_succ

/-!
# Causal integration: composition

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/CausalIntegration/Composition.lean`.  It is reconstructed
here as the composition theory of the causal operators introduced in
`Shared.CausalintegrationCore.CausalIntegration_Core`.

Main results:

* `CausalIntegration.isCausal_comp` — causal operators are closed under composition,
  so they form a monoid;
* `CausalIntegration.integrate_comp_diff` / `diff_comp_integrate` — integration and
  differencing are mutually inverse *as operators*;
* `CausalIntegration.iteratedIntegrate` and `iteratedIntegrate_isCausal` — the
  iterated running sum is causal;
* `CausalIntegration.integrate_two_eq_weighted` — the second running sum is the
  discrete Abel/Cauchy formula `∑_{k ≤ n} (n + 1 - k) f k`.
-/

open CausalIntegration











theorem iteratedIntegrate_succ (m n : ℕ) (f : Signal) :
    iteratedIntegrate (m + 1) f n = integrate (iteratedIntegrate m f) n := rfl

open CausalIntegration in
theorem solution(f : Signal) (n : ℕ) :
    iteratedIntegrate 2 f n = ∑ k ∈ Finset.range (n + 1), ((n + 1 - k : ℕ) : ℝ) * f k := by
  induction n with
  | zero => simp [iteratedIntegrate, integrate]
  | succ m ih =>
      have hstep : iteratedIntegrate 2 f (m + 1)
          = iteratedIntegrate 2 f m + integrate f (m + 1) := by
        simp only [iteratedIntegrate_succ, Function.comp_apply]
        exact integrate_succ _ m
      rw [hstep, ih, integrate,
        Finset.sum_range_succ (f := fun k => ((m + 1 + 1 - k : ℕ) : ℝ) * f k),
        Finset.sum_range_succ (f := f)]
      have hlast : ((m + 1 + 1 - (m + 1) : ℕ) : ℝ) = 1 := by norm_num
      rw [hlast, one_mul]
      have key : ∑ k ∈ Finset.range (m + 1), ((m + 1 + 1 - k : ℕ) : ℝ) * f k
          = ∑ k ∈ Finset.range (m + 1), (((m + 1 - k : ℕ) : ℝ) * f k + f k) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hc : ((m + 1 + 1 - k : ℕ) : ℝ) = ((m + 1 - k : ℕ) : ℝ) + 1 := by
          rw [show m + 1 + 1 - k = (m + 1 - k) + 1 by omega]
          push_cast
          ring
        rw [hc]
        ring
      rw [key, Finset.sum_add_distrib]
      ring
