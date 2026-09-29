-- Prove2me | solution 1 for Logic.QRDial.cov_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:46:51.505015+00:00
-- url     : https://prove2.me/submissions/837dff7b-f94c-4723-bbd1-696ed3304631

-- Sol generated from Logic/QRDialMultiCapture.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialMultiCapture
import Theorems.Thm_Logic_QRDial_avg_add
import Theorems.Thm_Logic_QRDial_avg_const
import Theorems.Thm_Logic_QRDial_cov_eq
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



lemma cov_add_left (x y z : ι → ℝ) :
    cov (fun i => x i + y i) z = cov x z + cov y z := by
  have h : (fun i => (x i + y i) * z i) = fun i => x i * z i + y i * z i := by
    funext i; ring
  rw [cov_eq, cov_eq, cov_eq, h]
  simp only [avg_add]
  ring





lemma cov_zero_left (z : ι → ℝ) : cov (fun _ => (0:ℝ)) z = 0 := by
  rw [cov_eq]
  simp




/-! ## The joint recalibration of a family of dials -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]








open Logic.QRDial in
theorem solution{κ : Type*} [DecidableEq κ] (t : Finset κ) (f : κ → ι → ℝ) (z : ι → ℝ) :
    cov (fun i => ∑ j ∈ t, f j i) z = ∑ j ∈ t, cov (f j) z := by
  classical
  induction t using Finset.induction with
  | empty => simpa using cov_zero_left z
  | insert a t ha ih =>
      have hfun : (fun i => ∑ j ∈ insert a t, f j i) = fun i => f a i + ∑ j ∈ t, f j i := by
        funext i; rw [Finset.sum_insert ha]
      rw [hfun, cov_add_left, ih, Finset.sum_insert ha]
