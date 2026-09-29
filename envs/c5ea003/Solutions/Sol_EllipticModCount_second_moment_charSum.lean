-- Prove2me | solution 1 for EllipticModCount.second_moment_charSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:52:47.66736+00:00
-- url     : https://prove2.me/submissions/b66bd1c5-0aa4-46c7-a784-dd0a9f1defaf

-- Sol generated from Combinatorics/EllipticSecondMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Theorems.Thm_EllipticModCount_sum_a_correlation
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
theorem solution(hF : ringChar F ≠ 2) :
    ∑ a : F, ∑ b : F, (charSum a b) ^ 2
      = (Fintype.card F : ℤ) ^ 3 - (Fintype.card F : ℤ) ^ 2 := by
  rw [Finset.sum_congr rfl fun a _ => sum_b_charSum_sq_eq_sum_ite hF a, Finset.sum_comm]
  have step2 : ∀ x : F, ∑ y : F, ∑ a : F,
      (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1)
      = (Fintype.card F : ℤ) ^ 2 - (Fintype.card F : ℤ) := by
    intro x
    rw [Finset.sum_congr rfl fun y _ => sum_a_correlation x y]
    rw [Finset.sum_ite_eq univ x (fun _ : F => (Fintype.card F : ℤ) ^ 2 - (Fintype.card F : ℤ))]
    simp
  have hswap : ∀ x : F, ∑ y : F, ∑ a : F,
      (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1)
      = ∑ a : F, ∑ y : F,
        (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1) :=
    fun x => Finset.sum_comm
  rw [Finset.sum_congr rfl fun x _ => ((hswap x).symm.trans (step2 x))]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring
