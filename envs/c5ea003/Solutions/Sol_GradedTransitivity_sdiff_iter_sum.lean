-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:52:51.427422+00:00
-- url     : https://prove2.me/submissions/32a50f52-5da5-42e3-815e-5ed48c809df8

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
theorem solution{ι : Type*} (s : Finset ι) (F : ι → ℕ → ℚ) :
    ∀ k : ℕ, sdiff^[k] (fun n => ∑ j ∈ s, F j n) = fun n => ∑ j ∈ s, sdiff^[k] (F j) n := by
  intro k
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have hs : sdiff (fun n => ∑ j ∈ s, F j n) = fun n => ∑ j ∈ s, sdiff (F j) n := by
        funext n
        simp [GradedTransitivity.sdiff, Finset.sum_sub_distrib]
      rw [hs, ih (fun j => sdiff (F j))]
      funext n
      simp [Function.iterate_succ_apply]
