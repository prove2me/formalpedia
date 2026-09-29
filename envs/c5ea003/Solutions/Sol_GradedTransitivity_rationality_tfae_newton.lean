-- Prove2me | solution 1 for GradedTransitivity.rationality_tfae_newton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:54:29.845339+00:00
-- url     : https://prove2.me/submissions/129ecdd7-a6b1-49bf-a170-fa1c29a3849d

-- Sol generated from Shared/GradedTransitivity/Newton.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_Newton
import Definitions.Def_Shared_GradedTransitivity_Structure
import Theorems.Thm_GradedTransitivity_newton_forward
import Theorems.Thm_GradedTransitivity_sdiff_iter_binomShift_eq_zero
import Theorems.Thm_GradedTransitivity_sdiff_iter_congr
import Theorems.Thm_GradedTransitivity_sdiff_iter_const_mul
import Theorems.Thm_GradedTransitivity_sdiff_iter_eq_zero_of_eq_zero
import Theorems.Thm_GradedTransitivity_sdiff_iter_eventuallyZero_iff
import Theorems.Thm_GradedTransitivity_sdiff_iter_sum

/-!
# Newton's forward-difference classification

This file closes the circle around the rationality criterion by proving the
missing *converse*: a sequence whose `k`-th forward difference vanishes
eventually is, from that point on, a `ℚ`-linear combination of the `k`
binomial functions `n ↦ C(n-N, j)`, `j < k` (Newton's forward difference
formula).  Together with `FiniteDifference` this yields the classification

`(1-q)^k` clears `∑ a n qⁿ`
  ⟺ `Δ^k a` vanishes eventually
  ⟺ `a` is eventually a combination of `C(·-N, j)`, `j < k`.

For a graded `G`-set this says: eventual `r`-transitivity is only the simplest
member of a hierarchy, and the exponent `k` in the denominator measures exactly
the binomial degree of the orbit-counting sequence.

## Main results

* `newton_forward` : Newton's forward difference formula.
* `sdiff_iter_binom_eq_zero` : the binomial functions are annihilated.
* `rationality_tfae_newton` : the three-way classification.
-/

open GradedTransitivity

open Polynomial

/-! ### Linearity of the difference operator -/




/-! ### The shifted binomial functions -/




/-- More generally `Δ^k` annihilates `n ↦ C(n-N, j)` past the shift whenever
`j < k`. -/
theorem sdiff_iter_binom_eq_zero {N j k : ℕ} (hjk : j < k) :
    ∀ n ≥ N, sdiff^[k] (binomShift N j) n = 0 := by
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m, k = m + (j + 1) := ⟨k - (j + 1), by omega⟩
  rw [hm, Function.iterate_add_apply]
  exact sdiff_iter_eq_zero_of_eq_zero (sdiff_iter_binomShift_eq_zero N j) m n hn

/-! ### Newton's forward difference formula -/





/-! ### The classification -/



open GradedTransitivity in
theorem solution(k : ℕ) (a : ℕ → ℚ) :
    ((∃ P : ℚ[X], (1 - PowerSeries.X) ^ k * gen a = (P : PowerSeries ℚ)) ↔
        EventuallyZero (sdiff^[k] a)) ∧
      (EventuallyZero (sdiff^[k] a) ↔
        ∃ (N : ℕ) (d : ℕ → ℚ), ∀ n ≥ N, a n = ∑ j ∈ Finset.range k, d j * binomShift N j n) := by
  refine ⟨sdiff_iter_eventuallyZero_iff k a, ?_, ?_⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun j => sdiff^[j] a N, fun n hn => newton_forward hN n hn⟩
  · rintro ⟨N, d, hd⟩
    refine ⟨N, fun n hn => ?_⟩
    have hsum : ∀ m ≥ N, sdiff^[k] (fun n => ∑ j ∈ Finset.range k, d j * binomShift N j n) m
        = 0 := by
      intro m hm
      rw [sdiff_iter_sum (Finset.range k) (fun j n => d j * binomShift N j n) k]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [sdiff_iter_const_mul (d j) (binomShift N j) k]
      show d j * sdiff^[k] (binomShift N j) m = 0
      rw [sdiff_iter_binom_eq_zero (Finset.mem_range.1 hj) m hm]
      ring
    have hcongr := sdiff_iter_congr k a
      (fun n => ∑ j ∈ Finset.range k, d j * binomShift N j n) N hd n hn
    rw [hcongr]
    exact hsum n hn
