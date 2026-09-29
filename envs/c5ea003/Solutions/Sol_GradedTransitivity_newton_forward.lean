-- Prove2me | solution 1 for GradedTransitivity.newton_forward
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:46:28.673308+00:00
-- url     : https://prove2.me/submissions/a2383b49-f864-4004-b683-95dc146ba60d

-- Sol generated from Shared/GradedTransitivity/Newton.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_Newton
import Definitions.Def_Shared_GradedTransitivity_Structure
import Theorems.Thm_GradedTransitivity_newton_zero
import Theorems.Thm_GradedTransitivity_sdiff_iter_shift

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
theorem solution{k N : ℕ} {a : ℕ → ℚ} (h : ∀ n ≥ N, sdiff^[k] a n = 0) :
    ∀ n ≥ N, a n = ∑ j ∈ Finset.range k, (sdiff^[j] a N) * (((n - N).choose j : ℚ)) := by
  intro n hn
  have hb : ∀ m, sdiff^[k] (fun m => a (N + m)) m = 0 := by
    intro m
    rw [sdiff_iter_shift N k a]
    exact h (N + m) (by omega)
  have hnew := newton_zero k (fun m => a (N + m)) hb (n - N)
  have hNn : N + (n - N) = n := by omega
  simp only [hNn] at hnew
  rw [hnew]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sdiff_iter_shift N j a]
  simp
