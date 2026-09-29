-- Prove2me | solution 1 for HigherPythagorean.abs_signed_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:04:43.139666+00:00
-- url     : https://prove2.me/submissions/cb46f3b9-d74b-4c89-9195-d04d88e154b3

-- Sol generated from Shared/HigherPythagorean/LorentzCore.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_LorentzCore

/-!
# The Lorentz form of signature `(n,1)`, its integral automorphisms, and the reflection move

This file sets up the general framework in which the Berggren tree of primitive Pythagorean
triples and its higher–dimensional analogues live:

* `lorentzJ n`   — the Gram matrix `diag(1,…,1,-1)` of the form `x₁²+…+xₙ² − y²`;
* `lorentzQ n v` — the form itself;
* `NullCone n`   — its integral null cone (`= ` Pythagorean `n`-tuples);
* `IsIntegralLorentz n M` — the integral automorphisms of the form.

Main results.

* `lorentzQ_mulVec` : integral Lorentz matrices preserve the form, hence the null cone
  (`IsIntegralLorentz.mapsTo_nullCone`).
* `IsIntegralLorentz.det_sq` : such matrices have determinant `±1`.
* `lorentz_move_height_bound` : the *sharp* growth constant of the reflection move in the
  all-ones vector: the height is multiplied by at most `(√n+1)/(√n−1)`.  For `n = 2` this is
  `3+2√2 = (1+√2)²`, the square of the silver ratio (Berggren); for `n = 3` it is `2+√3`.
* `refl_not_integral_of_four_le` : the all-ones reflection is *not* integral for `n ≥ 4`,
  so the Berggren mechanism only exists in dimensions `n = 2, 3`.
-/

open HigherPythagorean

open Matrix Finset


variable (n : ℕ)




variable {n}






variable {n : ℕ}










/-!
### The all-ones reflection and its growth constant

For the vector `r = (1,…,1;1)` one has `q(r) = n − 1` and the reflection
`s_r(v) = v − (2·B(v,r)/(n−1))·r` subtracts the *same* rational number from every coordinate.
Its effect on the height (last coordinate) is `y ↦ ((n+1)y − 2∑ εᵢxᵢ)/(n−1)`.
-/





/-!
### Failure of integrality for `n ≥ 4`

The reflection in the all-ones vector subtracts `c = 2·B(v,r)/(n−1)` from each coordinate.
Applied to the first basis vector this is `2/(n−1)`, which is an integer only for `n ≤ 3`.
Consequently the Berggren move exists over `ℤ` precisely in dimensions `n = 2` (triples) and
`n = 3` (quadruples).
-/





open HigherPythagorean in
lemma solution{n : ℕ} (x e : Fin n → ℝ) (y : ℝ) (hy : 0 < y)
    (h : ∑ i, (x i) ^ 2 = y ^ 2) (he : ∀ i, e i = 1 ∨ e i = -1) :
    |∑ i, e i * x i| ≤ Real.sqrt n * y := by
  have hsq : (∑ i, e i * x i) ^ 2 ≤ (n : ℝ) * y ^ 2 := by
    have hcs : (∑ i, e i * x i) ^ 2 ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) *
        ∑ i, (e i * x i) ^ 2 := sq_sum_le_card_mul_sum_sq
    have hval : ∑ i, (e i * x i) ^ 2 = ∑ i, (x i) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rcases he i with h1 | h1 <;> simp [h1]
    rw [hval, h] at hcs
    simpa using hcs
  have hs : Real.sqrt n * y = Real.sqrt ((n : ℝ) * y ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le]
  rw [hs]
  calc |∑ i, e i * x i| = Real.sqrt ((∑ i, e i * x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((n : ℝ) * y ^ 2) := Real.sqrt_le_sqrt hsq
