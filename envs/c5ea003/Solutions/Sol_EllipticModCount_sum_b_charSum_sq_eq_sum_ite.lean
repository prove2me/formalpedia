-- Prove2me | solution 1 for EllipticModCount.sum_b_charSum_sq_eq_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:51:17.128728+00:00
-- url     : https://prove2.me/submissions/fa2f15a9-9086-4dd2-aa25-f8f265540c7f

-- Sol generated from Combinatorics/EllipticSecondMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Theorems.Thm_EllipticModCount_sum_char_shift_pair
/-
# The exact second moment of the trace of Frobenius over a finite field

Let `F` be a finite field of odd characteristic, `q = #F`, and for `a b : F` let
`a(a,b)` be the trace of Frobenius of the short Weierstrass curve `y^2 = x^3+a*x+b`
(defined in `Combinatorics.EllipticPointCount`).  We prove the **exact** identity

`∑_{a,b ∈ F} a(a,b)^2 = q^3 - q^2`,

together with its Chebyshev consequence: the number of parameter pairs `(a,b)` with
`a(a,b)^2 ≥ K` is at most `(q^3 - q^2)/K`.  In particular *almost all* curves in the
family satisfy the Hasse bound `|a| ≤ 2√q`, by a purely elementary character-sum
computation (no Weil conjectures, no Riemann–Roch).

The engine is the elementary evaluation of the quadratic character sum of a
separable quadratic, `EllipticModCount.sum_char_mul_shift`.

Main results:

* `EllipticModCount.sum_char_mul_shift` : `∑_c χ(c(c+w)) = -1` for `w ≠ 0`.
* `EllipticModCount.sum_char_shift_pair` : `∑_b χ((b+u)(b+v)) = q-1` or `-1`.
* `EllipticModCount.second_moment_charSum` : `∑_{a,b} S(a,b)^2 = q^3 - q^2`.
* `EllipticModCount.second_moment_frobTrace` : the same for the trace of Frobenius.
* `EllipticModCount.card_large_frobTrace_le` : Chebyshev / "Hasse on average".
-/

open EllipticModCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]








/-- The square of the character sum expanded as a double sum. -/
theorem charSum_sq (a b : F) :
    (charSum a b) ^ 2 = ∑ x : F, ∑ y : F, quadraticChar F (wRHS a b x * wRHS a b y) := by
  rw [sq, charSum, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => (map_mul (quadraticChar F) _ _).symm
















open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) (a : F) :
    ∑ b : F, (charSum a b) ^ 2
      = ∑ x : F, ∑ y : F,
          (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1) := by
  rw [Finset.sum_congr rfl fun b _ => charSum_sq a b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hrw : ∀ b : F,
      wRHS a b x * wRHS a b y = (b + (x ^ 3 + a * x)) * (b + (y ^ 3 + a * y)) := by
    intro b
    rw [wRHS, wRHS]
    ring
  rw [Finset.sum_congr rfl fun b _ => congrArg (quadraticChar F) (hrw b),
    sum_char_shift_pair hF]
