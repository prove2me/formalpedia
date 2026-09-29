-- Prove2me | solution 1 for EllipticModCount.vertical_second_moment_zero_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:18:00.06898+00:00
-- url     : https://prove2.me/submissions/05704004-5e79-49ad-8092-006a4659283d

-- Sol generated from Combinatorics/EllipticVerticalMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment
import Theorems.Thm_EllipticModCount_collisions_formula
import Theorems.Thm_EllipticModCount_frobTrace_eq_neg_charSum
import Theorems.Thm_EllipticModCount_sum_b_charSum_sq
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














/-- The collision count for `a = 0`. -/
theorem collisions_zero (hF : ringChar F ≠ 2) (h3 : (3 : F) ≠ 0) :
    (collisions (0 : F) : ℤ)
      = 2 * (Fintype.card F : ℤ) - 1 + ((Fintype.card F : ℤ) - 1) * quadraticChar F (-3) := by
  rw [collisions_formula hF h3 0]
  simp only [neg_zero, zero_div, quadraticChar_zero, if_true]
  ring




/-- **Exact vertical second moment at `a = 0`.** -/
theorem vertical_second_moment_zero (hF : ringChar F ≠ 2) (h3 : (3 : F) ≠ 0) :
    ∑ b : F, (frobTrace (0 : F) b) ^ 2
      = (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) * (1 + quadraticChar F (-3)) := by
  have hconv : ∀ b : F, (frobTrace (0 : F) b) ^ 2 = (charSum (0 : F) b) ^ 2 := by
    intro b
    rw [frobTrace_eq_neg_charSum hF]
    ring
  rw [Finset.sum_congr rfl fun b _ => hconv b, sum_b_charSum_sq hF, collisions_zero hF h3]
  ring









open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (h3 : (3 : F) ≠ 0) :
    (∑ b : F, (frobTrace (0 : F) b) ^ 2 = 0) ↔ quadraticChar F (-3) = -1 := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqZ : (1 : ℤ) < (Fintype.card F : ℤ) := by exact_mod_cast hq
  rw [vertical_second_moment_zero hF h3]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h'' <;> linarith
    · linarith
  · intro h
    rw [h]
    ring
