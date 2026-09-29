-- Prove2me | solution 1 for EllipticModCount.sum_char_sq_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:56:06.319618+00:00
-- url     : https://prove2.me/submissions/cf78e93f-e18e-47fa-863e-c0ebb3f0342e

-- Sol generated from Combinatorics/EllipticVerticalMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment
import Theorems.Thm_EllipticModCount_sum_hyperbola
import Theorems.Thm_EllipticModCount_sum_ite_sq
/-
# Quadratic character sums, conic counts, and the exact vertical second moment

This file completes the elementary toolkit for the family `y^2 = x^3 + a*x + b` over a
finite field `F` of characteristic `≠ 2, 3` by evaluating **every** quadratic character
sum of a quadratic polynomial, counting the points of the conic `x^2+x*y+y^2 = c`, and
deducing the **exact vertical second moment**

`∑_{b ∈ F} a(a,b)^2 = q^2 - q * (1 + χ(-3) + χ(-3a))`  for `a ≠ 0`,
`∑_{b ∈ F} a(0,b)^2 = q * (q-1) * (1 + χ(-3))`.

The second formula gives a second, independent proof that the family `y^2 = x^3 + b` is
supersingular exactly when `χ(-3) = -1`, i.e. when `q ≡ 2 (mod 3)`.

Main results:

* `EllipticModCount.sum_char_quadratic` : `∑_v χ(αv^2+βv+γ) = -χ(α)` unless the
  discriminant vanishes, in which case it is `(q-1)χ(α)`.
* `EllipticModCount.sum_conic` : the number of points of `x^2+xy+y^2 = c`.
* `EllipticModCount.collisions_eq` / `collisions_zero` : exact collision counts.
* `EllipticModCount.vertical_second_moment` / `vertical_second_moment_zero`.
* `EllipticModCount.vertical_second_moment_zero_eq_zero_iff` : supersingularity of the
  family `y^2 = x^3 + b` is *equivalent* to `χ(-3) = -1`.
-/

open EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]



























open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (D : F) :
    ∑ u : F, quadraticChar F (u ^ 2 - D)
      = if D = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  have hkey : ∀ u : F, quadraticChar F (u ^ 2 - D)
      = (∑ t : F, (if t ^ 2 = u ^ 2 - D then (1 : ℤ) else 0)) - 1 := by
    intro u
    rw [sum_ite_sq hF]
    ring
  rw [Finset.sum_congr rfl fun u _ => hkey u, Finset.sum_sub_distrib, sum_hyperbola hF,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  by_cases hD : D = 0
  · rw [if_pos hD, if_pos hD]
    ring
  · rw [if_neg hD, if_neg hD]
    ring
