-- Prove2me | solution 1 for HigherPythagorean.lorentz_move_height_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:06:40.731727+00:00
-- url     : https://prove2.me/submissions/f1184153-3413-40e8-9bfc-708dfaeec4c8

-- Sol generated from Shared/HigherPythagorean/LorentzCore.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Theorems.Thm_HigherPythagorean_abs_signed_sum_le

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
theorem solution{n : ℕ} (hn : 2 ≤ n) (x e : Fin n → ℝ) (y : ℝ) (hy : 0 < y)
    (h : ∑ i, (x i) ^ 2 = y ^ 2) (he : ∀ i, e i = 1 ∨ e i = -1) :
    moveHeight n x e y ≤ (Real.sqrt n + 1) / (Real.sqrt n - 1) * y := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set s := Real.sqrt n with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hs1 : 1 < s := by nlinarith [hs2, hs0]
  have hb := abs_signed_sum_le x e y hy h he
  have hlow : -(s * y) ≤ ∑ i, e i * x i := by
    rcases abs_le.mp hb with ⟨h1, _⟩; linarith
  have hden : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hden' : (0 : ℝ) < s - 1 := by linarith
  rw [moveHeight, div_le_iff₀ hden]
  have key : ((n : ℝ) + 1) * y - 2 * ∑ i, e i * x i ≤ ((n : ℝ) + 1) * y + 2 * (s * y) := by
    linarith
  refine key.trans ?_
  have hfac : (s + 1) / (s - 1) * y * ((n : ℝ) - 1) = (s + 1) * (s + 1) * y := by
    field_simp
    nlinarith [hs2]
  rw [hfac]
  nlinarith [hs2, hy.le, hs0]
