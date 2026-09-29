-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_binomShift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:23:58.253252+00:00
-- url     : https://prove2.me/submissions/80449cba-0380-48e3-8a1c-7e0ae5ca687d

-- Sol generated from Shared/GradedTransitivity/Newton.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_Newton
import Definitions.Def_Shared_GradedTransitivity_Structure
import Theorems.Thm_GradedTransitivity_sdiff_iter_congr

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


/-- Past the shift, differencing lowers the binomial index. -/
theorem sdiff_binomShift (N j : ℕ) :
    ∀ n ≥ N, sdiff (binomShift N (j + 1)) n = binomShift N j n := by
  intro n hn
  have h1 : n + 1 - N = (n - N) + 1 := by omega
  simp only [GradedTransitivity.sdiff, binomShift, h1]
  rw [Nat.choose_succ_succ (n - N) j]
  push_cast
  ring



/-! ### Newton's forward difference formula -/





/-! ### The classification -/



open GradedTransitivity in
theorem solution(N : ℕ) :
    ∀ j : ℕ, ∀ n ≥ N, sdiff^[j + 1] (binomShift N j) n = 0 := by
  intro j
  induction j with
  | zero =>
      intro n _
      show sdiff (binomShift N 0) n = 0
      simp [GradedTransitivity.sdiff, binomShift]
  | succ j ih =>
      intro n hn
      rw [Function.iterate_succ_apply]
      have hcongr := sdiff_iter_congr (j + 1) (sdiff (binomShift N (j + 1))) (binomShift N j) N
        (fun m hm => sdiff_binomShift N j m hm) n hn
      rw [hcongr]
      exact ih n hn
