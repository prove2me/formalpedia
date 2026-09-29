-- Prove2me | solution 1 for EllipticModCount.sum_a_correlation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:48:06.165137+00:00
-- url     : https://prove2.me/submissions/09018f47-d080-4ce7-ad30-dd0eb5e84ef5

-- Sol generated from Combinatorics/EllipticSecondMoment.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
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
theorem solution(x y : F) :
    ∑ a : F, (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1)
      = if x = y then (Fintype.card F : ℤ) ^ 2 - (Fintype.card F : ℤ) else 0 := by
  by_cases h : x = y
  · subst h
    rw [if_pos rfl]
    have : ∀ a : F, (if x ^ 3 + a * x = x ^ 3 + a * x then (Fintype.card F : ℤ) - 1 else -1)
        = (Fintype.card F : ℤ) - 1 := by
      intro a
      rw [if_pos rfl]
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  · rw [if_neg h]
    have hxy : x - y ≠ 0 := sub_ne_zero.mpr h
    have hiff : ∀ a : F, (x ^ 3 + a * x = y ^ 3 + a * y) ↔ a = -(x ^ 2 + x * y + y ^ 2) := by
      intro a
      constructor
      · intro ha
        have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2 + a) = 0 := by linear_combination ha
        rcases mul_eq_zero.mp hfac with h' | h'
        · exact absurd h' hxy
        · linear_combination h'
      · intro ha
        rw [ha]
        ring
    have hstep : ∀ a : F,
        (if x ^ 3 + a * x = y ^ 3 + a * y then (Fintype.card F : ℤ) - 1 else -1)
          = -1 + (if a = -(x ^ 2 + x * y + y ^ 2) then (Fintype.card F : ℤ) else 0) := by
      intro a
      by_cases ha : a = -(x ^ 2 + x * y + y ^ 2)
      · rw [if_pos ((hiff a).mpr ha), if_pos ha]
        ring
      · rw [if_neg (fun hc => ha ((hiff a).mp hc)), if_neg ha]
        ring
    rw [Finset.sum_congr rfl fun a _ => hstep a, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq' univ (-(x ^ 2 + x * y + y ^ 2))
        (fun _ : F => (Fintype.card F : ℤ))]
    simp
