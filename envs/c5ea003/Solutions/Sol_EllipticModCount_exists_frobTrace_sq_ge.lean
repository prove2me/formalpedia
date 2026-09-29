-- Prove2me | solution 1 for EllipticModCount.exists_frobTrace_sq_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:02:41.914989+00:00
-- url     : https://prove2.me/submissions/8c668969-3d12-4a4e-b63e-ac81f7f8cd3f

-- Sol generated from Combinatorics/EllipticSecondMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Theorems.Thm_EllipticModCount_frobTrace_eq_neg_charSum
import Theorems.Thm_EllipticModCount_second_moment_charSum
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














/-- **Exact second moment of the trace of Frobenius.** -/
theorem second_moment_frobTrace (hF : ringChar F ≠ 2) :
    ∑ a : F, ∑ b : F, (frobTrace a b) ^ 2
      = (Fintype.card F : ℤ) ^ 3 - (Fintype.card F : ℤ) ^ 2 := by
  rw [← second_moment_charSum hF]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [frobTrace_eq_neg_charSum hF]
  ring










open EllipticModCount in
theorem solution(hF : ringChar F ≠ 2) :
    ∃ a b : F, (Fintype.card F : ℤ) - 1 ≤ (frobTrace a b) ^ 2 := by
  by_contra hcon
  push_neg at hcon
  have hbound : ∑ a : F, ∑ b : F, (frobTrace a b) ^ 2
      ≤ ∑ _a : F, ∑ _b : F, ((Fintype.card F : ℤ) - 2) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have := hcon a b
    omega
  rw [second_moment_frobTrace hF] at hbound
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hbound
  have hq : (1 : ℤ) ≤ (Fintype.card F : ℤ) := by
    have := Fintype.card_pos_iff.mpr (⟨0⟩ : Nonempty F)
    exact_mod_cast this
  nlinarith [hbound, hq]
