-- Prove2me | Theorems.Thm_Logic_QRDial_family_capture_bound_tight
-- name    : Logic.QRDial.family_capture_bound_tight
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:35:01.106277+00:00
-- url     : https://prove2.me/theorems/59e69c9f-2eed-4394-b521-096c85e62cc0
-- title:
--   The family bound is attained: coordinatewise OLS achieves it exactly.
-- statement:
--   The family bound is attained: coordinatewise OLS achieves it exactly.
--
--   ```lean
--   theorem Logic.QRDial.family_capture_bound_tight(y : ι → ℝ) (s : κ → ι → ℝ) (hs : ∀ j, 0 < var (s j))
--       (horth : ∀ j l, j ≠ l → cov (s j) (s l) = 0) :
--       mseFamily y s (avg y - ∑ j, (cov y (s j) / var (s j)) * avg (s j))
--           (fun j => cov y (s j) / var (s j))
--         = var y - ∑ j, (cov y (s j)) ^ 2 / var (s j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/QRDialMultiCapture.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/QRDialMultiCapture.lean#L194

-- Thm stub generated from Logic/QRDialMultiCapture.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialMultiCapture
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

theorem Logic.QRDial.family_capture_bound_tight(y : ι → ℝ) (s : κ → ι → ℝ) (hs : ∀ j, 0 < var (s j))
    (horth : ∀ j l, j ≠ l → cov (s j) (s l) = 0) :
    mseFamily y s (avg y - ∑ j, (cov y (s j) / var (s j)) * avg (s j))
        (fun j => cov y (s j) / var (s j))
      = var y - ∑ j, (cov y (s j)) ^ 2 / var (s j) := by sorry
