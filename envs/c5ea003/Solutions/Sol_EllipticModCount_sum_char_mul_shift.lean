-- Prove2me | solution 1 for EllipticModCount.sum_char_mul_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:48:06.750076+00:00
-- url     : https://prove2.me/submissions/185d63b7-e5d4-473e-add4-05309f957252

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
theorem solution(hF : ringChar F ≠ 2) {w : F} (hw : w ≠ 0) :
    ∑ c : F, quadraticChar F (c * (c + w)) = -1 := by
  have h0 : ∑ c : F, quadraticChar F (c * (c + w))
      = ∑ c ∈ univ.erase (0 : F), quadraticChar F (c * (c + w)) := by
    rw [Finset.sum_erase_eq_sub (mem_univ (0 : F))]
    simp
  have h1 : ∑ c ∈ univ.erase (0 : F), quadraticChar F (c * (c + w))
      = ∑ c ∈ univ.erase (0 : F), quadraticChar F (1 + w * c⁻¹) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    have hfac : c * (c + w) = c ^ 2 * (1 + w * c⁻¹) := by
      field_simp
    rw [hfac, map_mul, quadraticChar_sq_one' hc0, one_mul]
  have h2 : ∑ c ∈ univ.erase (0 : F), quadraticChar F (1 + w * c⁻¹)
      = ∑ t ∈ univ.erase (1 : F), quadraticChar F t := by
    refine Finset.sum_nbij' (i := fun c : F => 1 + w * c⁻¹) (j := fun t : F => w * (t - 1)⁻¹)
      ?_ ?_ ?_ ?_ ?_
    · intro c hc
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      refine Finset.mem_erase.mpr ⟨?_, mem_univ _⟩
      intro h
      have : w * c⁻¹ = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact hw h'
      · exact hc0 (inv_eq_zero.mp h')
    · intro t ht
      have ht1 : t ≠ 1 := (Finset.mem_erase.mp ht).1
      refine Finset.mem_erase.mpr ⟨?_, mem_univ _⟩
      exact mul_ne_zero hw (inv_ne_zero (sub_ne_zero.mpr ht1))
    · intro c hc
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      field_simp
      rw [show c + w - c = w from by ring, div_self hw]
    · intro t ht
      have ht1 : t ≠ 1 := (Finset.mem_erase.mp ht).1
      have h1' : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      field_simp
      ring
    · intro c _
      rfl
  have h3 : ∑ t ∈ univ.erase (1 : F), quadraticChar F t = -1 := by
    rw [Finset.sum_erase_eq_sub (mem_univ (1 : F)), quadraticChar_sum_zero hF]
    simp
  rw [h0, h1, h2, h3]
