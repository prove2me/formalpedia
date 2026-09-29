-- Prove2me | solution 1 for EllipticModCount.sum_b_charSum_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:10:58.689329+00:00
-- url     : https://prove2.me/submissions/7c7de91b-29a3-4ff4-bc16-49834f8ec093

-- Sol generated from Combinatorics/EllipticSecondMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Theorems.Thm_EllipticModCount_sum_b_charSum_sq_eq_sum_ite
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
theorem solution(hF : ringChar F ≠ 2) (a : F) :
    ∑ b : F, (charSum a b) ^ 2
      = (Fintype.card F : ℤ) * (collisions a : ℤ) - (Fintype.card F : ℤ) ^ 2 := by
  rw [sum_b_charSum_sq_eq_sum_ite hF a]
  have hconv : (∑ x : F, ∑ y : F,
      (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1))
      = ∑ xy : F × F,
        (if xy.1 ^ 3 + a * xy.1 = xy.2 ^ 3 + a * xy.2 then (Fintype.card F : ℤ) - 1 else -1) :=
    (Fintype.sum_prod_type' (fun x y : F =>
      if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1)).symm
  rw [hconv]
  have hstep : ∀ xy : F × F,
      (if xy.1 ^ 3 + a * xy.1 = xy.2 ^ 3 + a * xy.2 then (Fintype.card F : ℤ) - 1 else -1)
        = -1 + (if xy.1 ^ 3 + a * xy.1 = xy.2 ^ 3 + a * xy.2 then (Fintype.card F : ℤ) else 0) := by
    intro xy
    by_cases h : xy.1 ^ 3 + a * xy.1 = xy.2 ^ 3 + a * xy.2
    · simp [h]
      ring
    · simp [h]
  rw [Finset.sum_congr rfl fun xy _ => hstep xy, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Fintype.card_prod]
  push_cast
  rw [collisions]
  ring
