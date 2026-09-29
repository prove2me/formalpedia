-- Prove2me | solution 1 for EllipticModCount.sum_cardPoints_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:17:59.144849+00:00
-- url     : https://prove2.me/submissions/3c7384aa-d7b5-4a80-a75f-7bcb9b7e548f

-- Sol generated from Combinatorics/EllipticSecondMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Theorems.Thm_EllipticModCount_sum_frobTrace_over_b
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
























open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) :
    ∑ a : F, ∑ b : F, (cardPoints a b : ℤ)
      = (Fintype.card F : ℤ) ^ 2 * ((Fintype.card F : ℤ) + 1) := by
  have hpoint : ∀ a b : F, (cardPoints a b : ℤ)
      = ((Fintype.card F : ℤ) + 1) - frobTrace a b := by
    intro a b
    rw [frobTrace]
    ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpoint a b]
  have hinner : ∀ a : F, ∑ b : F, (((Fintype.card F : ℤ) + 1) - frobTrace a b)
      = (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) + 1) := by
    intro a
    rw [Finset.sum_sub_distrib, sum_frobTrace_over_b hF, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, sub_zero]
  rw [Finset.sum_congr rfl fun a _ => hinner a, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring
