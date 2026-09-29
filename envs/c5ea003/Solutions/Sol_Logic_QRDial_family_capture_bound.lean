-- Prove2me | solution 1 for Logic.QRDial.family_capture_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:02:18.039265+00:00
-- url     : https://prove2.me/submissions/8a15d245-ca36-4c72-a604-85984502c7cb

-- Sol generated from Logic/QRDialMultiCapture.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialMultiCapture
import Theorems.Thm_Logic_QRDial_mseFamily_expand
/-
# The capture ceiling of a whole orthogonal family of dials

The named follow-up of exp 576 is a product-form dial over *all* primes `ℓ ≤ 10⁶`
(~78k Legendre symbols) rather than the `ℓ ≤ 100` / `ℓ ≤ 400` windows already tested.
This file supplies the decision rule that such an experiment has to meet, in the form of an
exact finite-sample theorem rather than a fitted number.

For a finite family of dials `s : κ → ι → ℝ` that are pairwise uncorrelated across the
sample (which is what the independent-character model predicts for distinct primes, and
what `Logic.QRDial.cov_Sindiv_Sprod_eq_zero` proves for the two dials of exp 576), the
least-squares residual of the *joint* affine recalibration
`y ≈ a + Σ_j b_j · s_j` obeys

`mseFamily y s a b ≥ var y − Σ_j cov(y, s_j)² / var s_j`

(`Logic.QRDial.family_capture_bound`), with equality at the coordinatewise OLS
coefficients (`Logic.QRDial.family_capture_bound_tight`).  Consequently the total explained
fraction of an orthogonal family is the *sum of the individual squared correlations*, so
the pre-registered H1 bar (`30%`) can only be met if `Σ_j r_j² ≥ 0.30`
(`Logic.QRDial.family_bar_missed`).

Applied to the recorded exp-576 dials — `r² = 0.0127` and `r² = 0.0781`, which are
orthogonal by `cov_Sindiv_Sprod_eq_zero` — the family bound gives at most `9.1%`, and any
extension of the family to more primes must supply, in aggregate, more than `0.30` of
squared correlation to change the verdict.  That is a sharp, falsifiable target for the
`ℓ ≤ 10⁶` follow-up.

The technical core is the bilinearity of the sample covariance over finite sums
(`Logic.QRDial.cov_sum_left`), from which the exact quadratic expansion
`Logic.QRDial.mseFamily_expand` follows.
-/

open Finset

open Logic.QRDial

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Bilinearity of the sample covariance -/












/-! ## The joint recalibration of a family of dials -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]








open Logic.QRDial in
theorem solution(y : ι → ℝ) (s : κ → ι → ℝ) (hs : ∀ j, 0 < var (s j))
    (horth : ∀ j l, j ≠ l → cov (s j) (s l) = 0) (a : ℝ) (b : κ → ℝ) :
    var y - ∑ j, (cov y (s j)) ^ 2 / var (s j) ≤ mseFamily y s a b := by
  classical
  rw [mseFamily_expand]
  have hdiag : ∑ j, ∑ l, b j * b l * cov (s j) (s l)
      = ∑ j, (b j) ^ 2 * var (s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [var]; ring
    · intro l _ hl
      rw [horth j l (Ne.symm hl), mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hdiag]
  have hterm : ∀ j : κ, - ((cov y (s j)) ^ 2 / var (s j))
      ≤ -2 * (b j * cov y (s j)) + (b j) ^ 2 * var (s j) := by
    intro j
    have h1 : 0 ≤ (cov y (s j) - b j * var (s j)) ^ 2 / var (s j) :=
      div_nonneg (sq_nonneg _) (hs j).le
    have h2 : (cov y (s j) - b j * var (s j)) ^ 2 / var (s j)
        = (cov y (s j)) ^ 2 / var (s j) - 2 * (b j * cov y (s j)) + (b j) ^ 2 * var (s j) := by
      field_simp [(hs j).ne']; ring
    rw [h2] at h1
    linarith
  have hsum : ∑ j, (- ((cov y (s j)) ^ 2 / var (s j)))
      ≤ ∑ j, (-2 * (b j * cov y (s j)) + (b j) ^ 2 * var (s j)) :=
    Finset.sum_le_sum fun j _ => hterm j
  have hL : ∑ j, (- ((cov y (s j)) ^ 2 / var (s j)))
      = -∑ j, (cov y (s j)) ^ 2 / var (s j) := by
    rw [← Finset.sum_neg_distrib]
  have hR : ∑ j, (-2 * (b j * cov y (s j)) + (b j) ^ 2 * var (s j))
      = -2 * (∑ j, b j * cov y (s j)) + ∑ j, (b j) ^ 2 * var (s j) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hL, hR] at hsum
  nlinarith [hsum, sq_nonneg (avg y - a - ∑ j, b j * avg (s j))]
