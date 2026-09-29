-- Prove2me | solution 1 for HigherPythagorean.refl_not_integral_of_four_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:10:35.114346+00:00
-- url     : https://prove2.me/submissions/a635697b-0457-4398-96b7-4e0cf760db34

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
theorem solution(n : ℕ) (hn : 4 ≤ n) :
    ¬ ∃ z : ℤ, (2 : ℚ) / ((n : ℚ) - 1) = (z : ℚ) := by
  rintro ⟨z, hz⟩
  have hn4 : (4 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn1 : ((n : ℚ) - 1) ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hn4; norm_num at hn4
  have h2 : (2 : ℚ) = (z : ℚ) * ((n : ℚ) - 1) := by field_simp at hz; linarith
  have hZ : (2 : ℤ) = z * ((n : ℤ) - 1) := by
    have : ((2 : ℤ) : ℚ) = ((z * ((n : ℤ) - 1) : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hdvd : ((n : ℤ) - 1) ∣ 2 := ⟨z, by linarith⟩
  have hle : ((n : ℤ) - 1) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
  have h4 : (4 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  omega
