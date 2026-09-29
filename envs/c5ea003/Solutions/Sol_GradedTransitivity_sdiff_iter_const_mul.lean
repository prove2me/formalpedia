-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:52:49.70193+00:00
-- url     : https://prove2.me/submissions/2d799f6e-1435-4249-96b6-2122b141238c

-- Sol generated from Shared/GradedTransitivity/Newton.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_Newton
import Definitions.Def_Shared_GradedTransitivity_Structure

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





/-! ### Newton's forward difference formula -/





/-! ### The classification -/



open GradedTransitivity in
theorem solution(c : ℚ) (f : ℕ → ℚ) :
    ∀ k : ℕ, sdiff^[k] (fun n => c * f n) = fun n => c * sdiff^[k] f n := by
  intro k
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have hs : sdiff (fun n => c * f n) = fun n => c * sdiff f n := by
        funext n; simp [GradedTransitivity.sdiff]; try ring
      rw [hs, ih (sdiff f)]
      funext n
      simp [Function.iterate_succ_apply]
