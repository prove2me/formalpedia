-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_eq_zero_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:52:50.250077+00:00
-- url     : https://prove2.me/submissions/c28e2e1f-aa55-4023-9775-1fe41f89afe8

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





/-! ### Newton's forward difference formula -/





/-! ### The classification -/



open GradedTransitivity in
theorem solution{f : ℕ → ℚ} {N : ℕ} (h : ∀ n ≥ N, f n = 0) (k : ℕ) :
    ∀ n ≥ N, sdiff^[k] f n = 0 := by
  intro n hn
  have := sdiff_iter_congr k f (fun _ => 0) N (fun m hm => h m hm) n hn
  rw [this]
  clear this
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have : sdiff (fun _ : ℕ => (0 : ℚ)) = fun _ => 0 := by funext m; simp [GradedTransitivity.sdiff]
      rw [this]
      exact ih
