-- Prove2me | solution 1 for EllipticModCount.card_large_frobTrace_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:54:05.459722+00:00
-- url     : https://prove2.me/submissions/fa627330-b691-4ace-a1ad-e390090dc4f0

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
theorem solution(hF : ringChar F ≠ 2) (K : ℤ) :
    K * ((univ.filter fun ab : F × F => K ≤ (frobTrace ab.1 ab.2) ^ 2).card : ℤ)
      ≤ (Fintype.card F : ℤ) ^ 3 - (Fintype.card F : ℤ) ^ 2 := by
  classical
  set S : Finset (F × F) := univ.filter fun ab : F × F => K ≤ (frobTrace ab.1 ab.2) ^ 2 with hS
  have hlow : (S.card : ℤ) * K ≤ ∑ ab ∈ S, (frobTrace ab.1 ab.2) ^ 2 := by
    have := Finset.card_nsmul_le_sum S (fun ab : F × F => (frobTrace ab.1 ab.2) ^ 2) K
      (fun ab hab => (Finset.mem_filter.mp hab).2)
    simpa [nsmul_eq_mul, mul_comm] using this
  have hsub : ∑ ab ∈ S, (frobTrace ab.1 ab.2) ^ 2 ≤ ∑ ab : F × F, (frobTrace ab.1 ab.2) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro ab _ _
    positivity
  have htotal : ∑ ab : F × F, (frobTrace ab.1 ab.2) ^ 2
      = (Fintype.card F : ℤ) ^ 3 - (Fintype.card F : ℤ) ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact second_moment_frobTrace hF
  rw [← htotal]
  calc K * (S.card : ℤ) = (S.card : ℤ) * K := by ring
    _ ≤ ∑ ab ∈ S, (frobTrace ab.1 ab.2) ^ 2 := hlow
    _ ≤ ∑ ab : F × F, (frobTrace ab.1 ab.2) ^ 2 := hsub
