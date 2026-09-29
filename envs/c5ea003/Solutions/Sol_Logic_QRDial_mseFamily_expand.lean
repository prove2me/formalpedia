-- Prove2me | solution 1 for Logic.QRDial.mseFamily_expand
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:59:10.578726+00:00
-- url     : https://prove2.me/submissions/c6a056f3-e748-40f3-a9a9-b21bde63734b

-- Sol generated from Logic/QRDialMultiCapture.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialMultiCapture
import Theorems.Thm_Logic_QRDial_avg_add
import Theorems.Thm_Logic_QRDial_avg_const
import Theorems.Thm_Logic_QRDial_avg_mul_left
import Theorems.Thm_Logic_QRDial_cov_comm
import Theorems.Thm_Logic_QRDial_cov_eq
import Theorems.Thm_Logic_QRDial_cov_sum_left
import Theorems.Thm_Logic_QRDial_cov_sum_right
import Theorems.Thm_Logic_QRDial_var_eq
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

omit [Nonempty ι] in
lemma avg_sub (x y : ι → ℝ) : avg (fun i => x i - y i) = avg x - avg y := by
  have h : (fun i => x i - y i) = fun i => x i + (-1) * y i := by funext i; ring
  rw [h, avg_add, avg_mul_left]; ring

omit [Nonempty ι] in
/-- The sample average is additive over a finite sum. -/
lemma avg_sum {κ : Type*} [DecidableEq κ] (t : Finset κ) (f : κ → ι → ℝ) :
    avg (fun i => ∑ j ∈ t, f j i) = ∑ j ∈ t, avg (f j) := by
  classical
  induction t using Finset.induction with
  | empty => simp [avg]
  | insert a t ha ih =>
      have hfun : (fun i => ∑ j ∈ insert a t, f j i) = fun i => f a i + ∑ j ∈ t, f j i := by
        funext i; rw [Finset.sum_insert ha]
      rw [hfun, avg_add, ih, Finset.sum_insert ha]

lemma cov_add_left (x y z : ι → ℝ) :
    cov (fun i => x i + y i) z = cov x z + cov y z := by
  have h : (fun i => (x i + y i) * z i) = fun i => x i * z i + y i * z i := by
    funext i; ring
  rw [cov_eq, cov_eq, cov_eq, h]
  simp only [avg_add]
  ring

lemma cov_smul_left (c : ℝ) (x z : ι → ℝ) :
    cov (fun i => c * x i) z = c * cov x z := by
  have h : (fun i => c * x i * z i) = fun i => c * (x i * z i) := by funext i; ring
  rw [cov_eq, cov_eq, h]
  simp only [avg_mul_left]
  ring

lemma cov_smul_right (c : ℝ) (x z : ι → ℝ) :
    cov x (fun i => c * z i) = c * cov x z := by
  rw [cov_comm, cov_smul_left, cov_comm]

lemma cov_sub_left (x y z : ι → ℝ) :
    cov (fun i => x i - y i) z = cov x z - cov y z := by
  have h : (fun i => x i - y i) = fun i => x i + (-1) * y i := by funext i; ring
  rw [h, cov_add_left, cov_smul_left]; ring

lemma cov_sub_right (x y z : ι → ℝ) :
    cov x (fun i => y i - z i) = cov x y - cov x z := by
  rw [cov_comm, cov_sub_left, cov_comm y x, cov_comm z x]




/-- Squared error around an arbitrary centre splits into variance plus offset. -/
lemma avg_sq_sub_eq (u : ι → ℝ) (a : ℝ) :
    avg (fun i => (u i - a) ^ 2) = var u + (avg u - a) ^ 2 := by
  have h : (fun i => (u i - a) ^ 2)
      = fun i => (u i * u i) + ((-2 * a) * u i + a ^ 2) := by
    funext i; ring
  rw [h]
  simp only [avg_add, avg_mul_left, avg_const]
  rw [var_eq]
  ring

/-! ## The joint recalibration of a family of dials -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]








open Logic.QRDial in
theorem solution(y : ι → ℝ) (s : κ → ι → ℝ) (a : ℝ) (b : κ → ℝ) :
    mseFamily y s a b
      = var y - 2 * (∑ j, b j * cov y (s j))
        + (∑ j, ∑ l, b j * b l * cov (s j) (s l))
        + (avg y - a - ∑ j, b j * avg (s j)) ^ 2 := by
  classical
  set S : ι → ℝ := fun i => ∑ j, b j * s j i with hS
  have hmse : mseFamily y s a b = avg (fun i => ((y i - S i) - a) ^ 2) := by
    rw [mseFamily]
    exact congrArg avg (funext fun i => by rw [hS]; ring_nf)
  have havgS : avg S = ∑ j, b j * avg (s j) := by
    rw [hS, avg_sum]
    exact Finset.sum_congr rfl fun j _ => avg_mul_left _ _
  have hcovyS : cov y S = ∑ j, b j * cov y (s j) := by
    rw [hS, cov_sum_right]
    exact Finset.sum_congr rfl fun j _ => cov_smul_right _ _ _
  have hvarS : var S = ∑ j, ∑ l, b j * b l * cov (s j) (s l) := by
    rw [var, hS, cov_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cov_smul_left, cov_sum_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [cov_smul_right]; ring
  have hvaru : var (fun i => y i - S i) = var y - 2 * cov y S + var S := by
    rw [var, cov_sub_left, cov_sub_right, cov_sub_right, ← var, ← var, cov_comm S y]
    ring
  rw [hmse, avg_sq_sub_eq, hvaru, hcovyS, hvarS, avg_sub, havgS]
  ring
