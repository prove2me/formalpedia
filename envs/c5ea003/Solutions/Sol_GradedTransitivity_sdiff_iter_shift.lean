-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:45:07.423887+00:00
-- url     : https://prove2.me/submissions/1f8e63b4-6d65-4db6-82c3-1c66efb5ddbb

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
theorem solution(N : ℕ) :
    ∀ (k : ℕ) (a : ℕ → ℚ), sdiff^[k] (fun m => a (N + m)) = fun m => sdiff^[k] a (N + m) := by
  intro k
  induction k with
  | zero => intro a; simp
  | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply]
      have hs : sdiff (fun m => a (N + m)) = fun m => sdiff a (N + m) := by
        funext m
        rfl
      rw [hs, ih (sdiff a)]
      funext m
      rw [Function.iterate_succ_apply]
