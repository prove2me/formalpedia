-- Prove2me | solution 1 for Logic.QRDial.two_dial_capture_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:03:38.12906+00:00
-- url     : https://prove2.me/submissions/5219f367-a777-4b84-b75b-71912d20262e

-- Sol generated from Logic/QRDialOrthogonality.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialOrthogonality
import Theorems.Thm_Logic_QRDial_avg_add
import Theorems.Thm_Logic_QRDial_avg_const
import Theorems.Thm_Logic_QRDial_avg_mul_left
import Theorems.Thm_Logic_QRDial_cov_eq
import Theorems.Thm_Logic_QRDial_var_eq
/-
# Exact orthogonality of the individual-symbol and product-symbol QR dials

The exp-576 robustness catch asserts that the two small-prime quadratic-residue dials are
*analytically* uncorrelated under independent characters:

* `S_indiv = #{(ℓ, side) : Jac(ℓ, p) = +1 or Jac(ℓ, q) = +1}`, the individual-symbol count;
* `S_prod  = #{ℓ : N is a QR mod ℓ} = #{ℓ : Jac(ℓ,p)·Jac(ℓ,q) = +1}`, the product-symbol
  count, which is the dial that actually controls the divisibility carrier
  (`ℓ ∣ x² − N` is possible iff `Jac(ℓ,N) = +1`).

Modelling the pair of Legendre symbols at each of `k` primes as an independent uniform
pair of signs, this file proves `Cov(S_indiv, S_prod) = 0` **exactly**, for every `k`
(`Logic.QRDial.cov_Sindiv_Sprod_eq_zero`), not merely to the measured `r = −0.01`.

The mechanism is a one-prime identity (`Logic.QRDial.char_cov_single_prime`): on the
four-point space of sign pairs the centred individual count `(+1,+1) ↦ 1`, `(±1,∓1) ↦ 0`,
`(−1,−1) ↦ −1` is *odd* under global sign flip while the centred product indicator is
*even*, so their inner product cancels in pairs.  Independence across primes then
propagates the cancellation additively; this is proved by an induction over the number of
primes with the general lemma `Logic.QRDial.sum_pattern_prod`.

The consequence for the verdict is `Logic.QRDial.two_dial_capture_bound`: because the two
dials are orthogonal, their explained-variance shares simply add, so *no* joint affine
recalibration of both dials can explain more than `r₁² + r₂²`.  With the measured
`r₁² = 0.0127` and `r₂² = 0.0781` this leaves at least `90.9%` of the log-rate variance
unexplained (`Logic.QRDial.exp576_two_dial_residual`), well outside the pre-registered
H1 bar of `30%`.
-/

open Finset

open Logic.QRDial

/-! ## Two orthogonal dials: joint affine capture -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]


/-- Exact expansion of the two-dial recalibration error. -/
lemma mse2_expand (y s t : ι → ℝ) (a b c : ℝ) :
    mse2 y s t a b c = var y - 2 * b * cov y s - 2 * c * cov y t
      + b ^ 2 * var s + c ^ 2 * var t + 2 * b * c * cov s t
      + (avg y - a - b * avg s - c * avg t) ^ 2 := by
  have h : (fun i => (y i - (a + b * s i + c * t i)) ^ 2)
      = fun i => (y i * y i) + ((-2 * b) * (y i * s i) + ((-2 * c) * (y i * t i)
        + ((b * b) * (s i * s i) + ((c * c) * (t i * t i) + ((2 * b * c) * (s i * t i)
        + ((-2 * a) * y i + ((2 * a * b) * s i + ((2 * a * c) * t i + a ^ 2)))))))) := by
    funext i; ring
  rw [mse2, h]
  simp only [avg_add, avg_mul_left, avg_const]
  rw [var_eq, var_eq, var_eq, cov_eq, cov_eq, cov_eq]
  ring




/-! ## The character model: `k` primes, independent uniform sign pairs -/






















open Logic.QRDial in
theorem solution(y s t : ι → ℝ) (hs : 0 < var s) (ht : 0 < var t)
    (hst : cov s t = 0) (a b c : ℝ) :
    var y - (cov y s) ^ 2 / var s - (cov y t) ^ 2 / var t ≤ mse2 y s t a b c := by
  rw [mse2_expand, hst]
  have h1 : 0 ≤ (cov y s - b * var s) ^ 2 / var s := by positivity
  have h2 : (cov y s - b * var s) ^ 2 / var s
      = (cov y s) ^ 2 / var s - 2 * b * cov y s + b ^ 2 * var s := by
    field_simp; ring
  have h3 : 0 ≤ (cov y t - c * var t) ^ 2 / var t := by positivity
  have h4 : (cov y t - c * var t) ^ 2 / var t
      = (cov y t) ^ 2 / var t - 2 * c * cov y t + c ^ 2 * var t := by
    field_simp; ring
  have h0 : 0 ≤ (avg y - a - b * avg s - c * avg t) ^ 2 := sq_nonneg _
  rw [h2] at h1
  rw [h4] at h3
  linarith
