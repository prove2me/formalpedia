-- Prove2me | solution 1 for EllipticModCount.sum_ite_quadratic_root
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:57:30.377344+00:00
-- url     : https://prove2.me/submissions/3afd2000-29bc-46ed-82f1-a601dfc8356f

-- Sol generated from Combinatorics/EllipticVerticalMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment
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


/-- Multiplying by a nonzero square does not change the quadratic character. -/
theorem char_mul_sq {d : F} (hd : d ≠ 0) (c : F) :
    quadraticChar F (c * d ^ 2) = quadraticChar F c := by
  rw [map_mul, quadraticChar_sq_one' hd, mul_one]

























open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (β γ : F) :
    ∑ y : F, (if y ^ 2 + β * y + γ = 0 then (1 : ℤ) else 0)
      = quadraticChar F (β ^ 2 - 4 * γ) + 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hbij : Function.Bijective fun z : F => z - β / 2 := by
    constructor
    · intro z₁ z₂ h
      simpa using h
    · intro y
      exact ⟨y + β / 2, by ring⟩
  have hcond : ∀ z : F,
      ((z - β / 2) ^ 2 + β * (z - β / 2) + γ = 0) ↔ (z ^ 2 = (β ^ 2 - 4 * γ) * (2⁻¹) ^ 2) := by
    intro z
    constructor
    · intro h
      field_simp
      field_simp at h
      linear_combination h
    · intro h
      field_simp at h ⊢
      linear_combination h
  have hre : ∑ z : F, (if (z - β / 2) ^ 2 + β * (z - β / 2) + γ = 0 then (1 : ℤ) else 0)
      = ∑ y : F, (if y ^ 2 + β * y + γ = 0 then (1 : ℤ) else 0) :=
    Fintype.sum_bijective _ hbij _ _ fun _ => rfl
  rw [← hre, Finset.sum_congr rfl fun z _ => if_congr (hcond z) rfl rfl,
    sum_ite_sq hF, char_mul_sq (by simpa using h2)]
