-- Prove2me | solution 1 for Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:56:12.421863+00:00
-- url     : https://prove2.me/submissions/215b2bce-155a-4ce6-bf87-78d0921492ef

import Definitions.Def_erdos390_analytic_compact_goals
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_ContinuumCellGraph_IntervalMesh_abs_splitSharpEdge_cross_low_le
import Theorems.Thm_Erdos390_Full_FiniteManyLowRawGraphInverse_ordinary_raw_bound

/- Source module: Erdos390.Full.ConditionedPoissonLimit -/
section


/-!
# Exact analytic identities for the Poisson--Dickman bridge

This file continues the explicit finite-cutoff construction in
`ConditionedPoisson`.  The first layer below isolates the identities which
are needed by the covariance operator and proves them directly from the
method-of-steps Dickman equation.  In particular, the fact that the scale
function `t` is a null direction is not postulated.

The probability-theoretic exact-total projective limit is kept separate from
these analytic identities: this prevents a choice of a regular conditional
law on a null fibre from silently entering the operator calculation.
-/

open Filter Set
open scoped Interval BigOperators ENNReal NNReal

noncomputable section

namespace Erdos390.Full.ConditionedPoissonLimit

open MeasureTheory ProbabilityTheory Real
open DickmanBasic

/-! ## A global method-of-steps Dickman function -/













































































lemma covarianceKernel_comm (s t : ℝ) :
    covarianceKernel s t = covarianceKernel t s := by
  unfold covarianceKernel
  rw [add_comm]
  ring

















/-! ## Density-weighted Palm moments and covariance -/





/-! ## The removable axis singularity and a continuous kernel representative -/



















lemma covarianceKernelQuotient_eq_div {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (ht0 : t ≠ 0) :
    covarianceKernelQuotient s t = covarianceKernel s t / t := by
  apply (eq_div_iff ht0).2
  rw [mul_comm]
  exact mul_covarianceKernelQuotient_eq_kernel hs ht





























/-! ## The measurable Cauchy endpoint of the kernel argument -/





/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/







end Erdos390.Full.ConditionedPoissonLimit

end

/- Source module: Erdos390.Full.PoissonDickmanDirichlet -/
section


/-!
# A Dirichlet-form route for the Poisson--Dickman covariance kernel

This file isolates the deterministic part of the proposed kernel argument.
For a test function written as `f(t) = t * q(t)`, the covariance quadratic
form is exactly a symmetric Dirichlet energy.  The identity uses only the
Dickman averaging equation already proved in `ConditionedPoissonLimit`; it
does not use a conditional probability measure on the zero-probability
fibre.

The file also closes the sign of the Dirichlet kernel from the delay equation.
It formalizes the classical first-failure proof that the negative logarithmic
derivative of the Dickman function is strictly increasing on the required
range, turns this into the four-point log-concavity inequality, and hence
proves strict negativity of the covariance kernel in the open square.
-/

open Set
open scoped Interval

noncomputable section

namespace Erdos390.Full.PoissonDickmanDirichlet

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit

/-! ## Dickman log-concavity from a first-failure argument -/









































private lemma slopeIntegral_shift_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x in (U - s - t)..(U - s), dickmanLogSlope x) ≤
      ∫ x in (U - t)..U, dickmanLogSlope x := by
  have hab : U - s - t ≤ U - s := by linarith [ht.1]
  have hxmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.1, hx.2]
  have hxsmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x + s ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, hx.2]
  have hcont₁ : ContinuousOn dickmanLogSlope (Icc (U - s - t) (U - s)) :=
    continuousOn_dickmanLogSlope_one_to_nine_halves.mono hxmem
  have hcont₂ : ContinuousOn (fun x : ℝ => dickmanLogSlope (x + s))
      (Icc (U - s - t) (U - s)) := by
    apply continuousOn_dickmanLogSlope_one_to_nine_halves.comp
      (continuous_id.add continuous_const).continuousOn
    exact hxsmem
  have hmono : ∀ x ∈ Icc (U - s - t) (U - s),
      dickmanLogSlope x ≤ dickmanLogSlope (x + s) := by
    intro x hx
    apply strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
    · exact hxmem x hx
    · exact hxsmem x hx
    · linarith [hs.1]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hab
    (hcont₁.intervalIntegrable_of_Icc hab)
    (hcont₂.intervalIntegrable_of_Icc hab) hmono
  rw [intervalIntegral.integral_comp_add_right] at hint
  convert hint using 1
  ring



lemma log_rho_four_point_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.log (rho (U - s - t)) + Real.log (rho U) ≤
      Real.log (rho (U - s)) + Real.log (rho (U - t)) := by
  have h₁ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - s - t) (b := U - s)
    (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
    (by linarith [ht.1])
    (by norm_num [U] at hs ⊢; linarith [hs.1])
  have h₂ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - t) (b := U)
    (by norm_num [U] at ht ⊢; linarith [ht.2])
    (by linarith [ht.1]) (by norm_num [U])
  have hint := slopeIntegral_shift_le hs ht
  linarith



lemma rho_four_point_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    rho (U - s - t) * rho U ≤ rho (U - s) * rho (U - t) := by
  have ha : 0 < rho (U - s - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
      (by norm_num [U] at hs ht ⊢; linarith [hs.1, ht.1])
  have hb : 0 < rho U := rho_U_pos
  have hc : 0 < rho (U - s) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ⊢; linarith [hs.2])
      (by norm_num [U] at hs ⊢; linarith [hs.1])
  have hd : 0 < rho (U - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at ht ⊢; linarith [ht.2])
      (by norm_num [U] at ht ⊢; linarith [ht.1])
  have h := Real.exp_le_exp.mpr (log_rho_four_point_le hs ht)
  rw [Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb,
    Real.exp_log hc, Real.exp_log hd] at h
  exact h



/-- The covariance defect is nonpositive on the closed physical square.
This is now an unconditional theorem, obtained from the proved Dickman
log-concavity rather than supplied as an analytic premise. -/
theorem covarianceKernel_nonpos {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernel s t ≤ 0 := by
  have hprod := rho_four_point_le hs ht
  have hU : 0 < rho U := rho_U_pos
  have hden : 0 < rho U * rho U := mul_pos hU hU
  have hscaled := (div_le_div_iff_of_pos_right hden).2 hprod
  unfold covarianceKernel F
  apply sub_nonpos.mpr
  calc
    rho (U - (s + t)) / rho U =
        (rho (U - s - t) * rho U) / (rho U * rho U) := by
      rw [show U - (s + t) = U - s - t by ring]
      field_simp [ne_of_gt hU]
    _ ≤ (rho (U - s) * rho (U - t)) / (rho U * rho U) := hscaled
    _ = rho (U - s) / rho U * (rho (U - t) / rho U) := by
      field_simp [ne_of_gt hU]





































































/-! ## Unconditional covariance consequences -/















end Erdos390.Full.PoissonDickmanDirichlet

end

/- Source module: Erdos390.Full.PoissonDickmanWeightedInverse -/
section


/-!
# A deterministic weighted `L∞` quotient inverse

After writing the Poisson--Dickman test as `f(t)=t q(t)`, the covariance
operator is a nonlocal graph Laplacian with continuous edge kernel
`-K(s,t)/s`.  Strict Dickman log-concavity makes this edge kernel uniformly
positive when the second endpoint ranges in one fixed interior interval,
including at the removable axis `s=0`.  A maximum/minimum argument then
controls the oscillation of `q` directly.  This gives the weighted quotient
inverse without assuming Fredholm theory or an inverse theorem.
-/

open Set

noncomputable section

set_option maxHeartbeats 800000

namespace Erdos390.Full.PoissonDickmanWeightedInverse

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit PoissonDickmanDirichlet









/-! The strict four-point inequality with one endpoint allowed to equal one.
The proof repeats the already audited shifted-slope integral argument, but
uses only positivity (not strict upper bounds) for the endpoints. -/













/-! ## The weighted operator as a graph Laplacian -/







theorem covarianceKernelQuotient_transpose_nonpos {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernelQuotient t s ≤ 0 := by
  by_cases hs0 : s = 0
  · subst s
    rw [covarianceKernelQuotient_axis_formula ht]
    have hUt : U - t ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
      norm_num [U] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have hU : U ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by norm_num [U]
    have hslope : dickmanLogSlope (U - t) ≤ dickmanLogSlope U :=
      strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
        hUt hU (by linarith [ht.1])
    exact mul_nonpos_of_nonneg_of_nonpos
      (F_pos ⟨ht.1, ht.2.trans (by norm_num)⟩).le
      (sub_nonpos.mpr hslope)
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hkernel : covarianceKernel t s ≤ 0 :=
      covarianceKernel_nonpos ht hs
    have hmul := mul_covarianceKernelQuotient_eq_kernel
      (s := t) (t := s) ht hs
    nlinarith











end Erdos390.Full.PoissonDickmanWeightedInverse

end

/- Source module: Erdos390.Full.ContinuumCellGraph -/
section


/-!
# Continuum cell compression as a finite graph

This is the mesh-uniform bridge from the weighted Poisson--Dickman operator
to a finite matrix.  Every row is the ordinary-cell average of the graph
kernel `-K(t,s)/s`.  A fixed collection of cells lying in one interior
interval supplies a common anchor measure.  The positive edge constant is
derived from the Dickman kernel theorem; it is not mesh data.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph

open MeasureTheory
open ConditionedPoissonLimit
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band]



namespace IntervalMesh

variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)



omit [DecidableEq Band] in
theorem length_pos (i : Band) : 0 < M.length i :=
  sub_pos.mpr (M.lower_lt_upper i)







omit [DecidableEq Band] in
theorem cell_mem_unit {i : Band} {s : ℝ}
    (hs : s ∈ Icc (M.lower i) (M.upper i)) :
    s ∈ Icc (0 : ℝ) 1 :=
  ⟨(M.lower_pos i).le.trans hs.1, hs.2.trans (M.upper_le_one i)⟩

omit [DecidableEq Band] in
theorem interior_cell_mem {j : Band} (hj : j ∈ M.interiorCells)
    {t : ℝ} (ht : t ∈ Icc (M.lower j) (M.upper j)) :
    t ∈ Icc epsilon (1 - epsilon) :=
  ⟨(M.interior_lower j hj).trans ht.1,
    ht.2.trans (M.interior_upper j hj)⟩











/-! ## The exact edge matrix of the sharp continuum kernel block -/



omit [DecidableEq Band] in
theorem harmonicMass_pos (i : Band) : 0 < M.harmonicMass i := by
  unfold harmonicMass
  rw [integral_one_div_of_pos
    (M.lower_pos i) ((M.lower_pos i).trans (M.lower_lt_upper i))]
  apply Real.log_pos
  exact (one_lt_div (M.lower_pos i)).2 (M.lower_lt_upper i)



omit [DecidableEq Band] in
theorem center_pos (i : Band) : 0 < M.center i :=
  div_pos (M.length_pos i) (M.harmonicMass_pos i)





omit [DecidableEq Band] in
theorem sharpKernelEdge_eq_normalizedKernelCell (i j : Band) :
    M.sharpKernelEdge i j =
      -M.normalizedKernelCell i j * (M.center j / M.center i) := by
  have hmassI : M.harmonicMass i ≠ 0 :=
    ne_of_gt (M.harmonicMass_pos i)
  have hlengthI : M.length i ≠ 0 := ne_of_gt (M.length_pos i)
  unfold sharpKernelEdge normalizedKernelCell center
  have hneg : (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
      -(∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t) := by
    calc
      (∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            (-covarianceKernelQuotient t s) / t) =
          ∫ s in M.lower i..M.upper i,
            -(∫ t in M.lower j..M.upper j,
              covarianceKernelQuotient t s / t) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change (∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / t) =
            -(∫ t in M.lower j..M.upper j,
              covarianceKernelQuotient t s / t)
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = _ := intervalIntegral.integral_neg
  rw [hneg]
  field_simp [hmassI, hlengthI]

omit [DecidableEq Band] in
theorem sharpKernelEdge_nonneg (i j : Band) :
    0 ≤ M.sharpKernelEdge i j := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      0 ≤ ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t := by
    apply intervalIntegral.integral_nonneg
      (le_of_lt (M.lower_lt_upper j))
    intro t ht
    exact div_nonneg
      (neg_nonneg.mpr (covarianceKernelQuotient_transpose_nonpos
        (M.cell_mem_unit hs) (M.cell_mem_unit ht)))
      (le_trans (M.lower_pos j).le ht.1)
  have hdouble : 0 ≤ ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t :=
    intervalIntegral.integral_nonneg
      (le_of_lt (M.lower_lt_upper i)) hinner
  exact mul_nonneg
    (div_nonneg (M.center_pos j).le (M.length_pos i).le) hdouble

omit [DecidableEq Band] in
private theorem continuous_innerSharpEdge (j : Band) :
    Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) := by
  let d : ℝ → ℝ := fun t => max t (M.lower j / 2)
  have hdcont : Continuous d :=
    continuous_id.max
      (continuous_const : Continuous fun _ : ℝ => M.lower j / 2)
  have hd0 (t : ℝ) : d t ≠ 0 := by
    have hdpos : 0 < d t := by
      dsimp only [d]
      exact (half_pos (M.lower_pos j)).trans_le (le_max_right _ _)
    exact ne_of_gt hdpos
  have hsurrogate : Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / d t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := M.lower j) (b₀ := M.upper j)
    exact (continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).neg.div
        (hdcont.comp continuous_snd) (fun z => hd0 z.2)
  have heq : (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
      (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / d t) := by
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    have hhalf : M.lower j / 2 ≤ t := by
      linarith [M.lower_pos j, htcc.1]
    change (-covarianceKernelQuotient t s) / t =
      (-covarianceKernelQuotient t s) / d t
    rw [show d t = t by simp [d, max_eq_left hhalf] ]
  rw [heq]
  exact hsurrogate

/-- The sharp kernel-cell edge inherits the same mesh-independent anchor
domination, now in the exact normalization used by the arithmetic matrix. -/
theorem gap_mul_anchor_le_sharpKernelEdge
    {kappa : ℝ}
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (i j : Band) :
    kappa * M.anchor j ≤ M.sharpKernelEdge i j := by
  by_cases hj : j ∈ M.interiorCells
  · have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
        kappa * M.harmonicMass j ≤
          ∫ t in M.lower j..M.upper j,
            (-covarianceKernelQuotient t s) / t := by
      have hleft : IntervalIntegrable (fun t : ℝ => kappa / t) volume
          (M.lower j) (M.upper j) := by
        apply ContinuousOn.intervalIntegrable_of_Icc
          (le_of_lt (M.lower_lt_upper j))
        intro t ht
        exact (continuousAt_const.div continuousAt_id
          (ne_of_gt ((M.lower_pos j).trans_le ht.1))).continuousWithinAt
      have hright : IntervalIntegrable
          (fun t : ℝ => (-covarianceKernelQuotient t s) / t) volume
          (M.lower j) (M.upper j) := by
        apply ContinuousOn.intervalIntegrable_of_Icc
          (le_of_lt (M.lower_lt_upper j))
        intro t ht
        exact ((continuous_uncurry_covarianceKernelQuotient.comp
          (continuous_id.prodMk continuous_const)).neg.continuousAt.div
            continuousAt_id
            (ne_of_gt ((M.lower_pos j).trans_le ht.1))).continuousWithinAt
      have hmono := intervalIntegral.integral_mono_on
        (le_of_lt (M.lower_lt_upper j)) hleft hright
        (fun t ht => div_le_div_of_nonneg_right
          (hgap s (M.cell_mem_unit hs) t (M.interior_cell_mem hj ht))
          (le_trans (M.lower_pos j).le ht.1))
      calc
        kappa * M.harmonicMass j =
            ∫ t in M.lower j..M.upper j, kappa / t := by
          unfold harmonicMass
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t ht
          ring
        _ ≤ _ := hmono
    have hleftOuter : IntervalIntegrable
        (fun _ : ℝ => kappa * M.harmonicMass j) volume
        (M.lower i) (M.upper i) :=
      continuous_const.intervalIntegrable _ _
    have hrightOuter : IntervalIntegrable (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / t) volume
        (M.lower i) (M.upper i) := by
      exact (M.continuous_innerSharpEdge j).intervalIntegrable _ _
    have houter := intervalIntegral.integral_mono_on
      (le_of_lt (M.lower_lt_upper i)) hleftOuter hrightOuter hinner
    have hdouble :
        M.length i * (kappa * M.harmonicMass j) ≤
          ∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              (-covarianceKernelQuotient t s) / t := by
      calc
        M.length i * (kappa * M.harmonicMass j) =
            ∫ _s in M.lower i..M.upper i,
              kappa * M.harmonicMass j := by
          simp [length]
          ring
        _ ≤ _ := houter
    have hlengthI : 0 < M.length i := M.length_pos i
    have hmassJ : 0 < M.harmonicMass j := M.harmonicMass_pos j
    unfold anchor
    rw [if_pos hj]
    unfold sharpKernelEdge
    calc
      kappa * M.length j =
          (M.center j / M.length i) *
            (M.length i * (kappa * M.harmonicMass j)) := by
        unfold center
        field_simp [ne_of_gt hlengthI, ne_of_gt hmassJ]
      _ ≤ (M.center j / M.length i) *
          (∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              (-covarianceKernelQuotient t s) / t) :=
        mul_le_mul_of_nonneg_left hdouble
          (div_nonneg (M.center_pos j).le hlengthI.le)
  · unfold anchor
    rw [if_neg hj, mul_zero]
    exact M.sharpKernelEdge_nonneg i j



end IntervalMesh

end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.ContinuumSharpArithmeticTransfer -/
section


/-!
# From normalized arithmetic cells to the continuum graph

The exact sharp continuum matrix differs from its positive graph Laplacian
only by an explicit row residual.  Arithmetic quadrature errors, center
errors, and that residual are aggregated here into one sharp row budget.
No inverse or coercivity statement occurs among the hypotheses.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open CompressedArithmeticOperator
open DickmanBasic

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)







theorem continuumSharpOperator_eq_graph_add_residual
    (q : Band → ℝ) (i : Band) :
    M.continuumSharpOperator q i =
      FiniteGraphQuotientInverse.graphOperator M.sharpKernelEdge q i +
        M.rowResidual i * q i := by
  unfold continuumSharpOperator sharpOperator rowResidual
  have hedge (j : Band) :
      M.normalizedKernelCell i j * (M.center j / M.center i) =
        -M.sharpKernelEdge i j := by
    rw [M.sharpKernelEdge_eq_normalizedKernelCell]
    ring
  simp_rw [hedge]
  unfold FiniteGraphQuotientInverse.graphOperator
  have hgraph :
      (∑ j, M.sharpKernelEdge i j * (q i - q j)) =
        (∑ j, M.sharpKernelEdge i j) * q i -
          ∑ j, M.sharpKernelEdge i j * q j := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsumneg :
      (∑ x, (-M.sharpKernelEdge i x) * q x) =
        -(∑ x, M.sharpKernelEdge i x * q x) := by
    calc
      _ = ∑ x, -(M.sharpKernelEdge i x * q x) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by simp
  have hedgeneg :
      (∑ x, -M.sharpKernelEdge i x) =
        -(∑ x, M.sharpKernelEdge i x) := by simp
  rw [hgraph, hsumneg, hedgeneg]
  ring





end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperWeightedInverseExport -/
section


/-!
# Export of the sharp inverse in the paper's weighted band norm

The finite graph argument is naturally written after the diagonal change of
variables `b j = alpha j * q j`.  This file records the change of variables
as an exact linear equivalence between the two arithmetic gauges.  It also
proves that the projected raw row-normalized matrix is conjugate to
`projectedSharpLinearMap`.  Consequently an inverse estimate in the ordinary
supremum norm of `q` is literally the paper estimate
`max_j |b_j| / |alpha_j|` for the unscaled band coefficient `b`.

There is no limiting centre and no continuum gauge in this algebraic export.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open ArithmeticGaugeStableInverse
open CompressedArithmeticOperator
open FiniteGraphQuotientInverse
open FiniteGraphStableInverse
open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band]



















theorem rawOperator_scale_eq
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha q : Band → ℝ) (hAlpha : ∀ i, alpha i ≠ 0)
    (i : Band) :
    rawOperator diagonal kernel (scaleByCenter alpha q) i =
      alpha i * sharpOperator diagonal kernel alpha q i := by
  unfold rawOperator scaleByCenter sharpOperator
  have hsum :
      (∑ j, kernel i j * (alpha j * q j)) =
        alpha i * ∑ j, kernel i j * (alpha j / alpha i) * q j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hAlpha i]
  rw [hsum]
  ring





















end Erdos390.Full.PaperWeightedInverseExport

end

/- Source module: Erdos390.Full.FiniteReversibleGraph -/
section


/-!
# Reversible finite graph rows

The continuum cell graph used in the moving-low argument is reversible for
its harmonic-centre weight.  This file records the finite algebra needed to
turn detailed balance into the exact statement that projection to the gauge
does not change the graph row.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteReversibleGraph

open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]

/-- Detailed balance makes the weighted integral of a graph Laplacian
vanish.  No symmetry of `edge` itself is required. -/
theorem weighted_sum_graphOperator_eq_zero
    (edge : Band → Band → ℝ) (omega q : Band → ℝ)
    (hbalance : ∀ i j, omega i * edge i j = omega j * edge j i) :
    ∑ i, omega i * graphOperator edge q i = 0 := by
  classical
  unfold graphOperator
  have hswap :
      (∑ i, ∑ j, omega i * edge i j * q j) =
        ∑ i, ∑ j, omega i * edge i j * q i := by
    calc
      (∑ i, ∑ j, omega i * edge i j * q j) =
          ∑ j, ∑ i, omega i * edge i j * q j := Finset.sum_comm
      _ = ∑ j, ∑ i, omega j * edge j i * q j := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hbalance]
      _ = ∑ i, ∑ j, omega i * edge i j * q i := by
        rfl
  calc
    (∑ i, omega i * ∑ j, edge i j * (q i - q j)) =
        (∑ i, ∑ j, omega i * edge i j * q i) -
          ∑ i, ∑ j, omega i * edge i j * q j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = 0 := sub_eq_zero.mpr hswap.symm





end Erdos390.Full.FiniteReversibleGraph

end

/- Source module: Erdos390.Full.ContinuumCellGraphReversible -/
section


/-!
# Reversibility of the continuum cell graph

After the centre conjugation, the cell edge is reversible for the exact
sharp gauge weight `H_i alpha_i^2`.  The proof below keeps the moving low
cell: all divisions occur on its positive interval `[t₀,δ]`, and no lower
bound independent of `t₀` is used.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open FiniteGraphQuotientInverse
open FiniteReversibleGraph

variable {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

omit [DecidableEq Band] in
private theorem sharpEdgeIntegrand_comm
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    (-covarianceKernelQuotient t s) / t =
      (-covarianceKernelQuotient s t) / s := by
  rw [covarianceKernelQuotient_eq_div ht hs hs0,
    covarianceKernelQuotient_eq_div hs ht ht0,
    covarianceKernel_comm t s]
  field_simp [hs0, ht0]

omit [DecidableEq Band] in
private theorem doubleSharpIntegral_comm (i j : Band) :
    (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
    ∫ s in M.lower j..M.upper j,
      ∫ t in M.lower i..M.upper i,
        (-covarianceKernelQuotient t s) / t := by
  let g : ℝ → ℝ → ℝ := fun s t ↦
    (-covarianceKernelQuotient t s) / t
  let R : Set (ℝ × ℝ) :=
    Icc (M.lower i) (M.upper i) ×ˢ Icc (M.lower j) (M.upper j)
  have hg : ContinuousOn (Function.uncurry g) R := by
    intro z hz
    have htz : z.2 ≠ 0 :=
      ne_of_gt ((M.lower_pos j).trans_le hz.2.1)
    exact (((continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).neg).continuousAt.div
        continuousAt_snd htz).continuousWithinAt
  have hIntegrableOn : IntegrableOn (Function.uncurry g)
      (Ioc (M.lower i) (M.upper i) ×ˢ
        Ioc (M.lower j) (M.upper j)) := by
    apply (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hIntegrable : Integrable (Function.uncurry g)
      ((volume.restrict (Ioc (M.lower i) (M.upper i))).prod
        (volume.restrict (Ioc (M.lower j) (M.upper j)))) := by
    rw [Measure.prod_restrict]
    exact hIntegrableOn
  have hswap :
      (∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j, g s t) =
      ∫ t in M.lower j..M.upper j,
        ∫ s in M.lower i..M.upper i, g s t := by
    simp_rw [intervalIntegral.integral_of_le
      (le_of_lt (M.lower_lt_upper i)),
      intervalIntegral.integral_of_le
        (le_of_lt (M.lower_lt_upper j))]
    exact integral_integral_swap hIntegrable
  rw [show (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
      ∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j, g s t by rfl,
    hswap]
  apply intervalIntegral.integral_congr
  intro s _hs
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [g]
  have hscc : s ∈ Icc (M.lower j) (M.upper j) := by
    simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using _hs
  have htcc : t ∈ Icc (M.lower i) (M.upper i) := by
    simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using _ht
  exact sharpEdgeIntegrand_comm
    (M.cell_mem_unit htcc) (M.cell_mem_unit hscc)
    (ne_of_gt ((M.lower_pos i).trans_le htcc.1))
    (ne_of_gt ((M.lower_pos j).trans_le hscc.1))

omit [DecidableEq Band] in
/-- The exact harmonic-centre gauge weight equals `length * center`. -/
theorem harmonicMass_mul_center_sq_eq (i : Band) :
    M.harmonicMass i * M.center i ^ 2 = M.length i * M.center i := by
  unfold center
  field_simp [ne_of_gt (M.harmonicMass_pos i)]

omit [DecidableEq Band] in
/-- Exact detailed balance for the continuum sharp edge. -/
theorem sharpKernelEdge_detailedBalance (i j : Band) :
    (M.harmonicMass i * M.center i ^ 2) * M.sharpKernelEdge i j =
      (M.harmonicMass j * M.center j ^ 2) * M.sharpKernelEdge j i := by
  rw [M.harmonicMass_mul_center_sq_eq i,
    M.harmonicMass_mul_center_sq_eq j]
  unfold sharpKernelEdge
  rw [M.doubleSharpIntegral_comm i j]
  field_simp [ne_of_gt (M.length_pos i), ne_of_gt (M.length_pos j)]





end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.FiniteRawLowDiagonal -/
section


/-!
# Direct ordinary control of a low raw matrix row

Near the moving endpoint the continuum multiplier is close to one and the
product kernel has small row mass.  This elementary lemma records the exact
diagonal-dominance calculation in the ordinary coordinate supremum norm.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteRawLowDiagonal

open PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]

theorem abs_coordinate_le
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (b : Band → ℝ) (i : Band) {d k G : ℝ}
    (hd : |diagonal i - 1| ≤ d) (hdOne : d < 1)
    (hk : ∑ j : Band, |kernel i j| ≤ k)
    (hOutput : |rawOperator diagonal kernel b i| ≤ G) :
    |b i| ≤ (G + k * ‖b‖) / (1 - d) := by
  have hdiag : 1 - d ≤ diagonal i := by
    have := neg_le_of_abs_le hd
    linarith
  have hden : 0 < 1 - d := sub_pos.mpr hdOne
  have hdiagPos : 0 < diagonal i := hden.trans_le hdiag
  have hkernel : |∑ j : Band, kernel i j * b j| ≤ k * ‖b‖ := by
    calc
      |∑ j : Band, kernel i j * b j| ≤
          ∑ j : Band, |kernel i j * b j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Band, |kernel i j| * ‖b‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm b j)
          (abs_nonneg _)
      _ = (∑ j : Band, |kernel i j|) * ‖b‖ := by
        rw [← Finset.sum_mul]
      _ ≤ k * ‖b‖ :=
        mul_le_mul_of_nonneg_right hk (norm_nonneg b)
  have hscaled : (1 - d) * |b i| ≤ G + k * ‖b‖ := by
    calc
      (1 - d) * |b i| ≤ diagonal i * |b i| :=
        mul_le_mul_of_nonneg_right hdiag (abs_nonneg _)
      _ = |diagonal i * b i| := by
        rw [abs_mul, abs_of_pos hdiagPos]
      _ ≤ |rawOperator diagonal kernel b i| +
          |∑ j : Band, kernel i j * b j| := by
        have h := abs_sub (rawOperator diagonal kernel b i)
          (∑ j : Band, kernel i j * b j)
        unfold rawOperator at h
        simpa only [add_sub_cancel_right] using h
      _ ≤ G + k * ‖b‖ := add_le_add hOutput hkernel
  exact (le_div_iff₀ hden).2 (by
    simpa only [mul_comm] using hscaled)

end Erdos390.Full.FiniteRawLowDiagonal

end

/- Source module: Erdos390.Full.ContinuumRawLowRow -/
section


/-!
# Ordinary low-row bounds for the continuum cell compression

The product estimate `|K(s,t)| ≤ C s t` cancels both harmonic variables in
the compressed kernel.  Consequently the entire raw kernel row of a cell is
bounded by its harmonic centre, even when the mesh contains many cells below
a fixed cutoff.  This is the estimate that prevents the growing low harmonic
mass from entering the ordinary inverse.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- A product-kernel bound gives an exact raw continuum kernel-cell bound. -/
theorem abs_normalizedKernelCell_le_center_mul_length
    {C : ℝ}
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s * t)
    (i j : Band) :
    |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      |∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t| ≤ C * M.length j := by
    have hconst := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := M.lower j) (b := M.upper j) (C := C)
      (f := fun t : ℝ ↦ covarianceKernelQuotient t s / t) (by
        intro t ht
        have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
          simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using
            uIoc_subset_uIcc ht
        have hsUnit := M.cell_mem_unit hs
        have htUnit := M.cell_mem_unit htcc
        have hs0 : s ≠ 0 := ne_of_gt ((M.lower_pos i).trans_le hs.1)
        have ht0 : t ≠ 0 := ne_of_gt ((M.lower_pos j).trans_le htcc.1)
        change |covarianceKernelQuotient t s / t| ≤ C
        rw [covarianceKernelQuotient_eq_div htUnit hsUnit hs0,
          abs_div, abs_div, abs_of_pos ((M.lower_pos i).trans_le hs.1),
          abs_of_pos ((M.lower_pos j).trans_le htcc.1)]
        calc
          |covarianceKernel t s| / s / t ≤ (C * t * s) / s / t := by
            exact div_le_div_of_nonneg_right
              (div_le_div_of_nonneg_right (hKernel t htUnit s hsUnit)
                ((M.lower_pos i).trans_le hs.1).le)
              ((M.lower_pos j).trans_le htcc.1).le
          _ = C := by field_simp [hs0, ht0])
    rw [Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr (M.lower_lt_upper j))] at hconst
    simpa only [length] using hconst
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := M.lower i) (b := M.upper i) (C := C * M.length j)
    (f := fun s : ℝ ↦
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) (by
      intro s hs
      have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
        simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using
          uIoc_subset_uIcc hs
      simpa only [Real.norm_eq_abs] using hinner s hscc)
  have hmass : 0 < M.harmonicMass i := M.harmonicMass_pos i
  unfold normalizedKernelCell center
  rw [abs_div, abs_of_pos hmass]
  calc
    |∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t| / M.harmonicMass i ≤
      ((C * M.length j) * M.length i) / M.harmonicMass i := by
        apply div_le_div_of_nonneg_right _ hmass.le
        rw [Real.norm_eq_abs,
          abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] at houter
        simpa only [length] using houter
    _ = C * (M.length i / M.harmonicMass i) * M.length j := by ring

/-- Summing the preceding estimate over all input cells retains only their
total ordinary length, not their total harmonic mass. -/
theorem sum_abs_normalizedKernelCell_le
    {C totalLength : ℝ} (hC : 0 ≤ C)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s * t)
    (hLength : ∑ j : Band, M.length j ≤ totalLength)
    (i : Band) :
    ∑ j : Band, |M.normalizedKernelCell i j| ≤
      C * M.center i * totalLength := by
  calc
    ∑ j : Band, |M.normalizedKernelCell i j| ≤
        ∑ j : Band, C * M.center i * M.length j := by
      exact Finset.sum_le_sum fun j _ ↦
        M.abs_normalizedKernelCell_le_center_mul_length hKernel i j
    _ = (C * M.center i) * ∑ j : Band, M.length j := by
      rw [Finset.mul_sum]
    _ ≤ (C * M.center i) * totalLength :=
      mul_le_mul_of_nonneg_left hLength
        (mul_nonneg hC (M.center_pos i).le)





end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.ContinuumManyLowHighGeometry -/
section


/-!
# Low--high geometry for the ordinary continuum inverse

The ordinary inverse cannot be obtained from the sharp inverse by dividing
by the least cell centre: the centre of the moving low cell tends to zero.
This file instead records the exact estimates used after splitting a finite
continuum mesh into an arbitrary low block and a high block.  The product
kernel bound makes every edge entering a low cell proportional to both the
ordinary length and the centre of that cell.  Consequently all constants
below depend on the total low length, not on the number of low cells or on
their least endpoint.

No inverse, coercivity, or convergence statement is assumed here.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse

variable {Band Low High : Type*}
  [Fintype Band] [Fintype Low]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)







section Anchor

variable [DecidableEq Band]



omit [Fintype Low] in
/-- The high induced graph sees exactly the same fixed interior anchor. -/
theorem gap_mul_splitHighAnchor_le_highEdge
    (e : Sum Low High ≃ Band) {kappa : ℝ}
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (i j : High) :
    kappa * splitHighAnchor M e j ≤
      M.splitSharpEdge e (.inr i) (.inr j) := by
  exact M.gap_mul_anchor_le_sharpKernelEdge hgap
    (e (.inr i)) (e (.inr j))







end Anchor









end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.ContinuumProjectedRawOrdinary -/
section


/-!
# Ordinary bounds for the projected continuum raw operator

The continuum graph row is exactly gauge preserving.  The piecewise-centre
residual is not, so this file estimates its literal raw-gauge projection in
the ordinary supremum norm.  The estimate uses only the first-moment to
centre-energy ratio and therefore has no least-centre divisor.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open FiniteGraphQuotientInverse
open MovingLowGaugeTransfer
open PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)





/-- Exact raw-coordinate form of
`continuumSharpOperator_eq_graph_add_residual`. -/
theorem rawOperator_eq_scaledGraph_add_residual
    (b : Band → ℝ) (i : Band) :
    rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b i =
      M.center i * graphOperator M.sharpKernelEdge
          (fun j ↦ b j / M.center j) i + M.rowResidual i * b i := by
  let q : Band → ℝ := fun j ↦ b j / M.center j
  have hAlpha : ∀ j, M.center j ≠ 0 := fun j ↦ ne_of_gt (M.center_pos j)
  have hb : b = scaleByCenter M.center q := by
    funext j
    dsimp only [q, scaleByCenter]
    field_simp [hAlpha j]
  calc
    rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b i =
        rawOperator M.normalizedDiagonalCell M.normalizedKernelCell
          (scaleByCenter M.center q) i := by rw [← hb]
    _ = M.center i *
        CompressedArithmeticOperator.sharpOperator
          M.normalizedDiagonalCell M.normalizedKernelCell M.center q i :=
      rawOperator_scale_eq M.normalizedDiagonalCell M.normalizedKernelCell
        M.center q hAlpha i
    _ = M.center i * M.continuumSharpOperator q i := rfl
    _ = M.center i *
          (graphOperator M.sharpKernelEdge q i + M.rowResidual i * q i) := by
      rw [M.continuumSharpOperator_eq_graph_add_residual q i]
    _ = M.center i * graphOperator M.sharpKernelEdge
          (fun j ↦ b j / M.center j) i + M.rowResidual i * b i := by
      dsimp only [q]
      have hi : M.center i * (b i / M.center i) = b i := by
        field_simp [hAlpha i]
      calc
        M.center i *
            (graphOperator M.sharpKernelEdge
                (fun j ↦ b j / M.center j) i +
              M.rowResidual i * (b i / M.center i)) =
            M.center i * graphOperator M.sharpKernelEdge
                (fun j ↦ b j / M.center j) i +
              M.rowResidual i *
                (M.center i * (b i / M.center i)) := by ring
        _ = _ := by rw [hi]

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.ContinuumManyLowProjectedRawInverse -/
section


/-!
# Uniform ordinary inverse for the projected continuum cell operator

The unprojected continuum row is a reversible graph row plus the explicit
piecewise-centre residual.  This file projects that identity, proves the
direct low-row bound, invokes the many-low maximum principle, and performs
the final residual absorption.  Every smallness inequality appears in the
statement.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse
open FiniteRawLowDiagonal
open MovingLowGaugeTransfer
open PaperWeightedInverseExport

variable {Band Low High : Type*} [Fintype Band]
  [Fintype Low] [Fintype High]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Relabelling by a finite equivalence commutes exactly with the graph
operator. -/
theorem graphOperator_split_eq
    (e : Sum Low High ≃ Band) (q : Sum Low High → ℝ)
    (x : Sum Low High) :
    graphOperator (M.splitSharpEdge e) q x =
      graphOperator M.sharpKernelEdge (fun i ↦ q (e.symm i)) (e x) := by
  unfold graphOperator splitSharpEdge
  exact Fintype.sum_equiv e _ _ (fun j ↦ by simp)



end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.ContinuumManyLowArithmeticGaugeOrdinary -/
section


/-!
# Ordinary continuum inverse on a varying arithmetic gauge

The continuum graph is reversible for the continuum weight, whereas the
literal prime partition is projected with the arithmetic mass and centre.
This file performs that change of gauge without dividing by the least cell
centre.  The defect is measured in the raw weights `H * alpha`, and the
input gauge is represented exactly by the mixed weight
`H_a * alpha_a * alpha_c`.
-/

open scoped BigOperators
open Set

noncomputable section

set_option maxHeartbeats 800000

namespace Erdos390.Full.ContinuumCellGraph
namespace ArithmeticGaugeOrdinary

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse
open FiniteReversibleGraph
open FiniteRawLowDiagonal
open MovingLowGaugeTransfer
open PaperWeightedInverseExport

variable {Band Low High : Type*} [Fintype Band]
  [Fintype Low] [Fintype High]

/-- A raw weighted projection is bounded in ordinary norm by a scaled
first-moment/centre-energy ratio.  The scale `alphaMax` is explicit; in the
paper all centres are at most one. -/
theorem weightedGaugeProjection_norm_le_of_scaled_moment_ratio
    [Nonempty Band]
    (H alpha x : Band → ℝ) {alphaMax C R : ℝ}
    (hH : ∀ i, 0 ≤ H i)
    (hAlpha : ∀ i, 0 ≤ alpha i)
    (hAlphaUpper : ∀ i, alpha i ≤ alphaMax)
    (hTotal : 0 < sharpWeightTotal H alpha)
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hx : ∀ i, |x i| ≤ C)
    (hRatio : alphaMax * (∑ i : Band, H i * alpha i) ≤
      R * sharpWeightTotal H alpha) :
    ‖weightedGaugeProjection H alpha x‖ ≤ (1 + R) * C := by
  let total : ℝ := sharpWeightTotal H alpha
  let numerator : ℝ := ∑ i : Band, H i * alpha i * x i
  have hMoment : 0 ≤ ∑ i : Band, H i * alpha i :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hH i) (hAlpha i)
  have hAlphaMax : 0 ≤ alphaMax :=
    (hAlpha (Classical.choice (inferInstance : Nonempty Band))).trans
      (hAlphaUpper (Classical.choice (inferInstance : Nonempty Band)))
  have hnum : |numerator| ≤ C * (∑ i : Band, H i * alpha i) := by
    dsimp only [numerator]
    calc
      |∑ i : Band, H i * alpha i * x i| ≤
          ∑ i : Band, |H i * alpha i * x i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Band, C * (H i * alpha i) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul, abs_of_nonneg (hH i),
          abs_of_nonneg (hAlpha i)]
        calc
          H i * alpha i * |x i| ≤ (H i * alpha i) * C :=
            mul_le_mul_of_nonneg_left (hx i)
              (mul_nonneg (hH i) (hAlpha i))
          _ = C * (H i * alpha i) := by ring
      _ = C * (∑ i : Band, H i * alpha i) := by
        rw [Finset.mul_sum]
  have hmeanScaled : alphaMax * |numerator / total| ≤ R * C := by
    have ht : 0 < total := hTotal
    rw [abs_div, abs_of_pos ht]
    calc
      alphaMax * (|numerator| / total) ≤
          alphaMax * ((C * (∑ i : Band, H i * alpha i)) / total) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hnum ht.le) hAlphaMax
      _ = C * (alphaMax * (∑ i : Band, H i * alpha i)) / total := by
        ring
      _ ≤ C * (R * total) / total := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRatio hC) ht.le
      _ = R * C := by
        field_simp [ht.ne']
  have hbound : 0 ≤ (1 + R) * C := by positivity
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro i
  rw [Real.norm_eq_abs]
  unfold weightedGaugeProjection
  change |x i - alpha i * (numerator / total)| ≤ _
  calc
    |x i - alpha i * (numerator / total)| ≤
        |x i| + alpha i * |numerator / total| := by
      calc
        |x i - alpha i * (numerator / total)| ≤
            |x i| + |alpha i * (numerator / total)| := abs_sub _ _
        _ = |x i| + alpha i * |numerator / total| := by
          rw [abs_mul, abs_of_nonneg (hAlpha i)]
    _ ≤ C + alphaMax * |numerator / total| :=
      add_le_add (hx i)
        (mul_le_mul_of_nonneg_right (hAlphaUpper i) (abs_nonneg _))
    _ ≤ C + R * C := add_le_add le_rfl hmeanScaled
    _ = (1 + R) * C := by ring

/-- If a vector has zero continuum raw moment, changing to the arithmetic
raw projection moves it by at most the displayed raw-weight defect.  This
is the exact place where the two varying gauges are compared. -/
theorem weightedGaugeProjection_sub_self_norm_le_of_rawWeightDefect
    [Nonempty Band]
    (H alpha Hc alphac g : Band → ℝ)
    {alphaMax rho : ℝ}
    (hAlpha : ∀ i, 0 ≤ alpha i)
    (hAlphaUpper : ∀ i, alpha i ≤ alphaMax)
    (hTotal : 0 < sharpWeightTotal H alpha)
    (hContinuumMoment : ∑ i : Band, Hc i * alphac i * g i = 0)
    (hDefect : alphaMax *
        (∑ i : Band, |H i * alpha i - Hc i * alphac i|) ≤
      rho * sharpWeightTotal H alpha) :
    ‖weightedGaugeProjection H alpha g - g‖ ≤ rho * ‖g‖ := by
  let total : ℝ := sharpWeightTotal H alpha
  let numerator : ℝ := ∑ i : Band, H i * alpha i * g i
  let defect : ℝ :=
    ∑ i : Band, |H i * alpha i - Hc i * alphac i|
  have hAlphaMax : 0 ≤ alphaMax :=
    (hAlpha (Classical.choice (inferInstance : Nonempty Band))).trans
      (hAlphaUpper (Classical.choice (inferInstance : Nonempty Band)))
  have hDefectNonneg : 0 ≤ defect := by
    dsimp only [defect]
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hNumIdentity : numerator =
      ∑ i : Band, (H i * alpha i - Hc i * alphac i) * g i := by
    dsimp only [numerator]
    rw [show (∑ i : Band, H i * alpha i * g i) =
        (∑ i : Band, (H i * alpha i - Hc i * alphac i) * g i) +
          ∑ i : Band, Hc i * alphac i * g i by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [hContinuumMoment, add_zero]
  have hNum : |numerator| ≤ defect * ‖g‖ := by
    rw [hNumIdentity]
    calc
      |∑ i : Band, (H i * alpha i - Hc i * alphac i) * g i| ≤
          ∑ i : Band, |(H i * alpha i - Hc i * alphac i) * g i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Band,
          |H i * alpha i - Hc i * alphac i| * ‖g‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm g i)
          (abs_nonneg _)
      _ = defect * ‖g‖ := by
        dsimp only [defect]
        rw [Finset.sum_mul]
  have hRhoNonneg : 0 ≤ rho := by
    have hleft : 0 ≤ alphaMax * defect :=
      mul_nonneg hAlphaMax hDefectNonneg
    have hright : 0 ≤ rho * total := hleft.trans (by
      simpa only [defect, total] using hDefect)
    nlinarith [hTotal]
  have hbound : 0 ≤ rho * ‖g‖ := mul_nonneg hRhoNonneg (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro i
  rw [Real.norm_eq_abs]
  unfold weightedGaugeProjection
  change |g i - alpha i * (numerator / total) - g i| ≤ _
  rw [sub_sub_cancel_left, abs_neg, abs_mul,
    abs_of_nonneg (hAlpha i), abs_div, abs_of_pos hTotal]
  calc
    alpha i * (|numerator| / total) ≤
        alphaMax * ((defect * ‖g‖) / total) := by
      exact mul_le_mul (hAlphaUpper i)
        (div_le_div_of_nonneg_right hNum hTotal.le)
        (by positivity) hAlphaMax
    _ = (alphaMax * defect / total) * ‖g‖ := by ring
    _ ≤ rho * ‖g‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (div_le_iff₀ hTotal).2
      simpa only [total, defect] using hDefect

namespace IntervalMesh

variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Deterministic many-low inverse for an endpoint arithmetic raw operator.
The input and output live on the literal arithmetic gauge.  The continuum
graph enters only through explicit row, residual, and raw-weight errors;
neither the number of low cells nor their least centre occurs. -/
theorem ordinary_split_arithmetic_projected_raw_bound
    [DecidableEq Band] [Nonempty Band] [Nonempty High]
    (e : Sum Low High ≃ Band)
    (diagonalA : Band → ℝ) (kernelA : Band → Band → ℝ)
    (H alphaA : Band → ℝ)
    {C kappa amin amax alphaAMax lowCenter lowLength totalLength
      gaugeRatio d residual rowError R rho : ℝ}
    (hC : 0 ≤ C)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s * t)
    (hkappa : 0 < kappa)
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (hAnchorMassPos : 0 < ∑ i : High, M.splitHighAnchor e i)
    (hAmin : 0 < amin)
    (hHighCenterLower : ∀ i : High, amin ≤ M.center (e (.inr i)))
    (hHighCenterUpper : ∀ i : High, M.center (e (.inr i)) ≤ amax)
    (hAmax : 0 ≤ amax)
    (hLowCenterNonneg : 0 ≤ lowCenter)
    (hLowCenter : ∀ l : Low, M.center (e (.inl l)) ≤ lowCenter)
    (hLowLengthNonneg : 0 ≤ lowLength)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (hTotalLengthNonneg : 0 ≤ totalLength)
    (hTotalLength : ∑ i : Band, M.length i ≤ totalLength)
    (hH : ∀ i, 0 < H i) (hAlphaA : ∀ i, 0 < alphaA i)
    (hAlphaAUpper : ∀ i, alphaA i ≤ alphaAMax)
    (hMixedGaugeRatio :
      (∑ l : Low, H (e (.inl l)) * alphaA (e (.inl l))) ≤
        gaugeRatio *
          (∑ i : High, H (e (.inr i)) * alphaA (e (.inr i)) *
            M.center (e (.inr i))))
    (hdOne : d < 1)
    (hDiagonalLow : ∀ l : Low,
      |M.normalizedDiagonalCell (e (.inl l)) - 1| ≤ d)
    (hResidualNonneg : 0 ≤ residual)
    (hResidual : ∀ i : Band, |M.rowResidual i| ≤ residual)
    (hRowErrorNonneg : 0 ≤ rowError)
    (hRowError : ∀ b : RawGaugeSpace H alphaA, ∀ i : Band,
      |rawOperator diagonalA kernelA b.1 i -
          rawOperator M.normalizedDiagonalCell M.normalizedKernelCell
            b.1 i| ≤ rowError * ‖b‖)
    (hR : 0 ≤ R)
    (hMomentRatio : alphaAMax * (∑ i : Band, H i * alphaA i) ≤
      R * sharpWeightTotal H alphaA)
    (hRhoHalf : rho ≤ 1 / 2)
    (hRawWeightDefect : alphaAMax *
        (∑ i : Band,
          |H i * alphaA i - M.harmonicMass i * M.center i|) ≤
      rho * sharpWeightTotal H alphaA)
    (hAbsorbLow :
      let epsLow :=
        (residual + C * lowCenter * totalLength) / (1 - d)
      max epsLow
        (amax *
          (2 * (1 / (kappa *
              ∑ i : High, M.splitHighAnchor e i)) *
              ((C * lowCenter * lowLength) / amin +
                (C * lowLength) * epsLow) +
            gaugeRatio * epsLow)) ≤ 1 / 2)
    (hAbsorbArithmetic :
      let Clow := 1 / (1 - d)
      let Cmain :=
        max Clow
          (amax *
            (2 * (1 / (kappa *
                ∑ i : High, M.splitHighAnchor e i)) *
                (1 / amin + (C * lowLength) * Clow) +
              gaugeRatio * Clow))
      4 * Cmain * ((1 + R) * (rowError + residual)) ≤ 1 / 2)
    (b : RawGaugeSpace H alphaA) :
    ‖b‖ ≤
      (8 *
        max (1 / (1 - d))
          (amax *
            (2 * (1 / (kappa *
                ∑ i : High, M.splitHighAnchor e i)) *
                (1 / amin +
                  (C * lowLength) * (1 / (1 - d))) +
              gaugeRatio * (1 / (1 - d))))) *
        ‖projectedRawLinearMap diagonalA kernelA H alphaA
          (ne_of_gt (by
            unfold sharpWeightTotal sharpWeight
            apply Finset.sum_pos
            · intro i _hi
              exact mul_pos (hH i) (sq_pos_of_pos (hAlphaA i))
            · exact Finset.univ_nonempty)) b‖ := by
  let totalA : ℝ := sharpWeightTotal H alphaA
  have hTotalA : 0 < totalA := by
    dsimp only [totalA, sharpWeightTotal, sharpWeight]
    apply Finset.sum_pos
    · intro i hi
      exact mul_pos (hH i) (sq_pos_of_pos (hAlphaA i))
    · exact Finset.univ_nonempty
  let qBand : Band → ℝ := fun i ↦ b.1 i / M.center i
  let q : Sum Low High → ℝ := fun x ↦ qBand (e x)
  let graph : Band → ℝ := fun i ↦
    M.center i * graphOperator M.sharpKernelEdge qBand i
  let continuumRaw : Band → ℝ :=
    rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b.1
  let arithmeticRaw : Band → ℝ := rawOperator diagonalA kernelA b.1
  let projected : Band → ℝ :=
    weightedGaugeProjection H alphaA arithmeticRaw
  let B : ℝ := ‖b‖
  let G : ℝ := ‖projected‖
  let E : ℝ := rowError + residual
  let Ggraph : ℝ := 2 * G + 2 * ((1 + R) * E) * B
  let Clow : ℝ := 1 / (1 - d)
  let epsLow : ℝ :=
    (residual + C * lowCenter * totalLength) / (1 - d)
  let Cmain : ℝ :=
    max Clow
      (amax *
        (2 * (1 / (kappa *
            ∑ i : High, M.splitHighAnchor e i)) *
            (1 / amin + (C * lowLength) * Clow) +
          gaugeRatio * Clow))
  have hB : 0 ≤ B := norm_nonneg _
  have hG : 0 ≤ G := norm_nonneg _
  have hE : 0 ≤ E := add_nonneg hRowErrorNonneg hResidualNonneg
  have hGgraph : 0 ≤ Ggraph := by dsimp only [Ggraph]; positivity
  have hClow : 0 ≤ Clow := by
    dsimp only [Clow]
    exact one_div_nonneg.mpr (sub_pos.mpr hdOne).le
  have hepsLow : 0 ≤ epsLow := by
    dsimp only [epsLow]
    exact div_nonneg
      (add_nonneg hResidualNonneg
        (mul_nonneg (mul_nonneg hC hLowCenterNonneg)
          hTotalLengthNonneg))
      (sub_pos.mpr hdOne).le
  have hCmain : 0 ≤ Cmain :=
    hClow.trans (by dsimp only [Cmain]; exact le_max_left _ _)
  have hbPoint (i : Band) : |b.1 i| ≤ B := by
    dsimp only [B]
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm b.1 i
  have hqScale (i : Band) : M.center i * qBand i = b.1 i := by
    dsimp only [qBand]
    field_simp [ne_of_gt (M.center_pos i)]
  have hContinuumDecomp : continuumRaw = graph +
      fun i ↦ M.rowResidual i * b.1 i := by
    funext i
    have h := M.rawOperator_eq_scaledGraph_add_residual b.1 i
    simpa only [continuumRaw, graph, qBand] using h
  have hGraphContinuumMoment :
      ∑ i : Band, M.harmonicMass i * M.center i * graph i = 0 := by
    dsimp only [graph]
    calc
      (∑ i : Band, M.harmonicMass i * M.center i *
          (M.center i * graphOperator M.sharpKernelEdge qBand i)) =
        ∑ i : Band, (M.harmonicMass i * M.center i ^ 2) *
          graphOperator M.sharpKernelEdge qBand i := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = 0 := weighted_sum_graphOperator_eq_zero M.sharpKernelEdge
        (fun i ↦ M.harmonicMass i * M.center i ^ 2) qBand
        M.sharpKernelEdge_detailedBalance
  have hProjectionDefect :
      ‖weightedGaugeProjection H alphaA graph - graph‖ ≤ rho * ‖graph‖ := by
    exact weightedGaugeProjection_sub_self_norm_le_of_rawWeightDefect
      H alphaA M.harmonicMass M.center graph
      (fun i ↦ (hAlphaA i).le) hAlphaAUpper hTotalA
      hGraphContinuumMoment hRawWeightDefect
  let z : Band → ℝ := arithmeticRaw - graph
  have hzPoint (i : Band) : |z i| ≤ E * B := by
    have hrow := hRowError b i
    have hres := hResidual i
    have hdecomp := congrFun hContinuumDecomp i
    simp only [Pi.add_apply] at hdecomp
    dsimp only [z, arithmeticRaw, Pi.sub_apply]
    have hid : arithmeticRaw i - graph i =
        (arithmeticRaw i - continuumRaw i) + M.rowResidual i * b.1 i := by
      rw [hdecomp]
      ring
    rw [hid]
    calc
      |arithmeticRaw i - continuumRaw i + M.rowResidual i * b.1 i| ≤
          |arithmeticRaw i - continuumRaw i| +
            |M.rowResidual i * b.1 i| := abs_add_le _ _
      _ ≤ rowError * B + residual * B := by
        rw [abs_mul]
        exact add_le_add (by simpa only [arithmeticRaw, continuumRaw, B]
          using hrow)
          (mul_le_mul hres (hbPoint i) (abs_nonneg _)
            hResidualNonneg)
      _ = E * B := by dsimp only [E]; ring
  have hzProjected :
      ‖weightedGaugeProjection H alphaA z‖ ≤ (1 + R) * (E * B) := by
    exact weightedGaugeProjection_norm_le_of_scaled_moment_ratio
      H alphaA z (fun i ↦ (hH i).le) (fun i ↦ (hAlphaA i).le)
      hAlphaAUpper hTotalA (mul_nonneg hE hB) hR hzPoint hMomentRatio
  have hProjectedDecomp : projected =
      weightedGaugeProjection H alphaA graph +
        weightedGaugeProjection H alphaA z := by
    have harith : arithmeticRaw = graph + z := by
      funext i
      dsimp only [z]
      simp
    dsimp only [projected]
    rw [harith, weightedGaugeProjection_add]
  have hProjectedGraph :
      ‖weightedGaugeProjection H alphaA graph‖ ≤
        G + (1 + R) * (E * B) := by
    have hid : weightedGaugeProjection H alphaA graph =
        projected - weightedGaugeProjection H alphaA z := by
      rw [hProjectedDecomp]
      abel
    rw [hid]
    exact (norm_sub_le _ _).trans
      (add_le_add (by simpa only [G] using le_rfl) hzProjected)
  have hGraphNorm : ‖graph‖ ≤ Ggraph := by
    have htri : ‖graph‖ ≤
        ‖weightedGaugeProjection H alphaA graph‖ +
          ‖weightedGaugeProjection H alphaA graph - graph‖ := by
      have hid : graph = weightedGaugeProjection H alphaA graph -
          (weightedGaugeProjection H alphaA graph - graph) := by abel
      calc
        ‖graph‖ = ‖weightedGaugeProjection H alphaA graph -
            (weightedGaugeProjection H alphaA graph - graph)‖ :=
          congrArg norm hid
        _ ≤ _ := norm_sub_le _ _
    have hraw : ‖graph‖ ≤
        G + (1 + R) * (E * B) + rho * ‖graph‖ :=
      htri.trans (add_le_add hProjectedGraph hProjectionDefect)
    have hscaled : rho * ‖graph‖ ≤ (1 / 2) * ‖graph‖ :=
      mul_le_mul_of_nonneg_right hRhoHalf (norm_nonneg _)
    dsimp only [Ggraph]
    nlinarith
  have hGraphOutput (x : Sum Low High) :
      |M.center (e x) *
          graphOperator (M.splitSharpEdge e) q x| ≤ Ggraph := by
    have hrelabel := M.graphOperator_split_eq e q x
    rw [hrelabel]
    have hqRelabel : (fun i ↦ q (e.symm i)) = qBand := by
      funext i
      dsimp only [q]
      rw [e.apply_symm_apply]
    rw [hqRelabel]
    change |graph (e x)| ≤ Ggraph
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm graph (e x)).trans hGraphNorm
  have hLowDirect (l : Low) :
      |M.center (e (.inl l)) * q (.inl l)| ≤
        Clow * Ggraph + epsLow * B := by
    let i : Band := e (.inl l)
    have hrawOutput : |continuumRaw i| ≤ Ggraph + residual * B := by
      have hdecomp := congrFun hContinuumDecomp i
      simp only [Pi.add_apply] at hdecomp
      calc
        |continuumRaw i| = |graph i + M.rowResidual i * b.1 i| := by
          rw [hdecomp]
        _ ≤ |graph i| + |M.rowResidual i * b.1 i| := abs_add_le _ _
        _ ≤ Ggraph + residual * B := by
          exact add_le_add
            (by simpa only [Real.norm_eq_abs] using
              (norm_le_pi_norm graph i).trans hGraphNorm)
            (by rw [abs_mul]
                exact mul_le_mul (hResidual i) (hbPoint i)
                  (abs_nonneg _) hResidualNonneg)
    have hkernel :
        ∑ j : Band, |M.normalizedKernelCell i j| ≤
          C * lowCenter * totalLength := by
      have hrow := M.sum_abs_normalizedKernelCell_le hC hKernel hTotalLength i
      have hci : M.center i ≤ lowCenter := hLowCenter l
      exact hrow.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hci hC) hTotalLengthNonneg)
    have hdirect := FiniteRawLowDiagonal.abs_coordinate_le
      M.normalizedDiagonalCell M.normalizedKernelCell b.1 i
      (hDiagonalLow l) hdOne hkernel hrawOutput
    have hnum :
        Ggraph + residual * B +
            (C * lowCenter * totalLength) * ‖b.1‖ ≤
          Ggraph + (residual + C * lowCenter * totalLength) * B := by
      have hnorm : ‖b.1‖ = B := rfl
      rw [hnorm]
      ring_nf
      exact le_refl
        (Ggraph + residual * B + B * C * lowCenter * totalLength)
    have hden : 0 < 1 - d := sub_pos.mpr hdOne
    have hbq : b.1 i = M.center i * q (.inl l) := by
      dsimp only [i, q]
      rw [hqScale]
    rw [hbq] at hdirect
    calc
      |M.center i * q (.inl l)| ≤
          (Ggraph + residual * B +
            (C * lowCenter * totalLength) * ‖b.1‖) / (1 - d) :=
        hdirect
      _ ≤ (Ggraph +
          (residual + C * lowCenter * totalLength) * B) / (1 - d) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = Clow * Ggraph + epsLow * B := by
        dsimp only [Clow, epsLow]
        ring
  let omega : Sum Low High → ℝ := fun x ↦
    H (e x) * alphaA (e x) * M.center (e x)
  have hGauge : ∑ x : Sum Low High, omega x * q x = 0 := by
    calc
      (∑ x : Sum Low High, omega x * q x) =
          ∑ i : Band, H i * alphaA i * b.1 i := by
        apply Fintype.sum_equiv e
        intro x
        dsimp only [omega, q, qBand]
        field_simp [ne_of_gt (M.center_pos (e x))]
      _ = 0 := by
        have hbGauge := b.2
        change ∑ i : Band, H i * alphaA i * b.1 i = 0 at hbGauge
        exact hbGauge
  have hOmegaHigh (i : High) : 0 ≤ omega (.inr i) := by
    dsimp only [omega]
    exact mul_nonneg
      (mul_nonneg (hH _).le (hAlphaA _).le) (M.center_pos _).le
  have hOmegaHighTotal : 0 < ∑ i : High, omega (.inr i) := by
    apply Finset.sum_pos
    · intro i hi
      dsimp only [omega]
      exact mul_pos (mul_pos (hH _) (hAlphaA _)) (M.center_pos _)
    · exact Finset.univ_nonempty
  have hGaugeLow :
      |∑ l : Low, omega (.inl l) * q (.inl l)| ≤
        gaugeRatio * (∑ i : High, omega (.inr i)) *
          (Clow * Ggraph + epsLow * B) := by
    calc
      |∑ l : Low, omega (.inl l) * q (.inl l)| ≤
          ∑ l : Low, (H (e (.inl l)) * alphaA (e (.inl l))) *
            (Clow * Ggraph + epsLow * B) := by
        calc
          |∑ l : Low, omega (.inl l) * q (.inl l)| ≤
              ∑ l : Low, |omega (.inl l) * q (.inl l)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ l : Low,
                (H (e (.inl l)) * alphaA (e (.inl l))) *
                (Clow * Ggraph + epsLow * B) := by
            apply Finset.sum_le_sum
            intro l hl
            have hterm : |omega (.inl l) * q (.inl l)| =
                (H (e (.inl l)) * alphaA (e (.inl l))) *
                  |M.center (e (.inl l)) * q (.inl l)| := by
              dsimp only [omega]
              rw [abs_mul, abs_mul,
                abs_of_pos (mul_pos (hH _) (hAlphaA _)),
                abs_of_pos (M.center_pos _), abs_mul,
                abs_of_pos (M.center_pos _)]
              ring
            rw [hterm]
            exact mul_le_mul_of_nonneg_left (hLowDirect l)
              (mul_nonneg (hH _).le (hAlphaA _).le)
      _ = (∑ l : Low, H (e (.inl l)) * alphaA (e (.inl l))) *
          (Clow * Ggraph + epsLow * B) := by rw [Finset.sum_mul]
      _ ≤ gaugeRatio * (∑ i : High, omega (.inr i)) *
          (Clow * Ggraph + epsLow * B) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [omega] using hMixedGaugeRatio
  have hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤
        C * M.center i * M.length j :=
    M.abs_normalizedKernelCell_le_center_mul_length hKernel
  have hCrossRows (i : High) :
      |∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) *
          (q (.inr i) - q (.inl l))| ≤
        (C * lowCenter * lowLength) * B / amin +
          (C * lowLength) * (Clow * Ggraph + epsLow * B) := by
    exact M.abs_splitSharpEdge_cross_low_le e hC hLowCenterNonneg hB
      (by positivity) hCell hLowCenter hLowLength hAmin
      hHighCenterLower q (by
        intro x
        have hx : M.center (e x) * q x = b.1 (e x) := by
          dsimp only [q]
          rw [hqScale]
        rw [hx]
        exact hbPoint (e x)) hLowDirect i
  have hSplitNorm :
      ‖fun x ↦ M.center (e x) * q x‖ = B := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg hB]
      intro x
      rw [Real.norm_eq_abs]
      have hx : M.center (e x) * q x = b.1 (e x) := by
        dsimp only [q]
        rw [hqScale]
      rw [hx]
      exact hbPoint (e x)
    · change ‖b.1‖ ≤ _
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro i
      rw [Real.norm_eq_abs]
      let x := e.symm i
      have hx : M.center (e x) * q x = b.1 i := by
        dsimp only [x, q]
        rw [e.apply_symm_apply, hqScale]
      rw [← hx]
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (fun x ↦ M.center (e x) * q x) x
  have hBase := FiniteManyLowRawGraphInverse.ordinary_raw_bound
    (M.splitSharpEdge e) (M.splitHighAnchor e) omega
    (fun x ↦ M.center (e x)) q hGgraph hkappa rfl hAnchorMassPos
    (M.gap_mul_splitHighAnchor_le_highEdge e hgap)
    hHighCenterLower hAmin hHighCenterUpper
    (fun i ↦ (M.center_pos _).le) hAmax
    (mul_nonneg (mul_nonneg hC hLowCenterNonneg) hLowLengthNonneg)
    (mul_nonneg hC hLowLengthNonneg) hClow hepsLow hOmegaHigh
    hOmegaHighTotal hGauge hGraphOutput (by
      intro l
      rw [hSplitNorm]
      exact hLowDirect l) (by
      intro i
      rw [hSplitNorm]
      exact hCrossRows i) (by
      rw [hSplitNorm]
      exact hGaugeLow)
    (by simpa only [epsLow] using hAbsorbLow)
  have hBNorm : B ≤ 2 * Cmain * Ggraph := by
    have hnonneg : 0 ≤ 2 * Cmain * Ggraph := by positivity
    change ‖b.1‖ ≤ _
    rw [pi_norm_le_iff_of_nonneg hnonneg]
    intro i
    rw [Real.norm_eq_abs]
    let x := e.symm i
    have hx := hBase x
    have hid : M.center (e x) * q x = b.1 i := by
      dsimp only [x, q]
      rw [e.apply_symm_apply, hqScale]
    rw [hid] at hx
    simpa only [Cmain, Clow] using hx
  have hSmall : 4 * Cmain * ((1 + R) * E) ≤ 1 / 2 := by
    simpa only [Cmain, Clow, E] using hAbsorbArithmetic
  have hFinal : B ≤ 8 * Cmain * G := by
    have hraw : B ≤ 4 * Cmain * G +
        (4 * Cmain * ((1 + R) * E)) * B := by
      calc
        B ≤ 2 * Cmain * Ggraph := hBNorm
        _ = 4 * Cmain * G +
            (4 * Cmain * ((1 + R) * E)) * B := by
          dsimp only [Ggraph]
          ring
    have habsorb : (4 * Cmain * ((1 + R) * E)) * B ≤
        (1 / 2) * B := mul_le_mul_of_nonneg_right hSmall hB
    have hhalf : B ≤ 4 * Cmain * G + (1 / 2) * B :=
      hraw.trans (add_le_add le_rfl habsorb)
    linarith
  simpa only [B, G, projected, Cmain, Clow] using hFinal

end IntervalMesh
end ArithmeticGaugeOrdinary
end Erdos390.Full.ContinuumCellGraph

end

universe u_1 u_2 u_3
theorem solution :
∀ {Band : Type u_1} {Low : Type u_2} {High : Type u_3} [inst : Fintype.{u_1} Band] [inst_1 : Fintype.{u_2} Low]
  [inst_2 : Fintype.{u_3} High] {epsilon : Real} (M : Erdos390.Full.ContinuumCellGraph.IntervalMesh.{u_1} epsilon Band)
  [inst_3 : DecidableEq.{u_1 + 1} Band] [inst_4 : Nonempty.{u_1 + 1} Band] [Nonempty.{u_3 + 1} High]
  (e : Equiv.{max (u_3 + 1) (u_2 + 1), u_1 + 1} (Sum.{u_2, u_3} Low High) Band) (diagonalA : Band → Real)
  (kernelA : Band → Band → Real) (H alphaA : Band → Real)
  {C kappa amin amax alphaAMax lowCenter lowLength totalLength gaugeRatio d residual rowError R rho : Real},
  LE.le.{0} (0 : Real) C →
    (∀ (s : Real),
        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
          ∀ (t : Real),
            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
              LE.le.{0} (abs.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s t))
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C s) t)) →
      LT.lt.{0} (0 : Real) kappa →
        (∀ (s : Real),
            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
              ∀ (t : Real),
                Membership.mem.{0, 0} (Set.Icc.{0} epsilon (HSub.hSub.{0, 0, 0} (1 : Real) epsilon)) t →
                  LE.le.{0} kappa (Neg.neg.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernelQuotient t s))) →
          LT.lt.{0} (0 : Real)
              (∑ i, Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1, u_2, u_3} M e i) →
            LT.lt.{0} (0 : Real) amin →
              (∀ (i : High),
                  LE.le.{0} amin
                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))) →
                (∀ (i : High),
                    LE.le.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))
                      amax) →
                  LE.le.{0} (0 : Real) amax →
                    LE.le.{0} (0 : Real) lowCenter →
                      (∀ (l : Low),
                          LE.le.{0}
                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                            lowCenter) →
                        LE.le.{0} (0 : Real) lowLength →
                          LE.le.{0}
                              (∑ l,
                                Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                              lowLength →
                            LE.le.{0} (0 : Real) totalLength →
                              LE.le.{0} (∑ i, Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M i)
                                  totalLength →
                                ∀ (hH : ∀ (i : Band), LT.lt.{0} (0 : Real) (H i))
                                  (hAlphaA : ∀ (i : Band), LT.lt.{0} (0 : Real) (alphaA i)),
                                  (∀ (i : Band), LE.le.{0} (alphaA i) alphaAMax) →
                                    LE.le.{0}
                                        (∑ l,
                                          HMul.hMul.{0, 0, 0} (H (e (Sum.inl.{u_2, u_3} l)))
                                            (alphaA (e (Sum.inl.{u_2, u_3} l))))
                                        (HMul.hMul.{0, 0, 0} gaugeRatio
                                          (∑ i,
                                            HMul.hMul.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0} (H (e (Sum.inr.{u_2, u_3} i)))
                                                (alphaA (e (Sum.inr.{u_2, u_3} i))))
                                              (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M
                                                (e (Sum.inr.{u_2, u_3} i))))) →
                                      LT.lt.{0} d (1 : Real) →
                                        (∀ (l : Low),
                                            LE.le.{0}
                                              (abs.{0}
                                                (HSub.hSub.{0, 0, 0}
                                                  (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedDiagonalCell.{u_1}
                                                    M (e (Sum.inl.{u_2, u_3} l)))
                                                  (1 : Real)))
                                              d) →
                                          LE.le.{0} (0 : Real) residual →
                                            (∀ (i : Band),
                                                LE.le.{0}
                                                  (abs.{0}
                                                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.rowResidual.{u_1} M
                                                      i))
                                                  residual) →
                                              LE.le.{0} (0 : Real) rowError →
                                                (∀
                                                    (b :
                                                      ↥(Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{u_1} H
                                                          alphaA))
                                                    (i : Band),
                                                    LE.le.{0}
                                                      (abs.{0}
                                                        (HSub.hSub.{0, 0, 0}
                                                          (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
                                                            diagonalA kernelA (↑b) i)
                                                          (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
                                                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedDiagonalCell.{u_1}
                                                              M)
                                                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedKernelCell.{u_1}
                                                              M)
                                                            (↑b) i)))
                                                      (HMul.hMul.{0, 0, 0} rowError (Norm.norm.{u_1} b))) →
                                                  LE.le.{0} (0 : Real) R →
                                                    LE.le.{0}
                                                        (HMul.hMul.{0, 0, 0} alphaAMax
                                                          (∑ i, HMul.hMul.{0, 0, 0} (H i) (alphaA i)))
                                                        (HMul.hMul.{0, 0, 0} R
                                                          (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_1} H
                                                            alphaA)) →
                                                      LE.le.{0} rho (1 / 2 : Real) →
                                                        LE.le.{0}
                                                            (HMul.hMul.{0, 0, 0} alphaAMax
                                                              (∑ i,
                                                                abs.{0}
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} (H i) (alphaA i))
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (Erdos390.Full.ContinuumCellGraph.IntervalMesh.harmonicMass.{u_1}
                                                                        M i)
                                                                      (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1}
                                                                        M i)))))
                                                            (HMul.hMul.{0, 0, 0} rho
                                                              (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_1}
                                                                H alphaA)) →
                                                          (have epsLow :=
                                                              HDiv.hDiv.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0} residual
                                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C lowCenter)
                                                                    totalLength))
                                                                (HSub.hSub.{0, 0, 0} (1 : Real) d);
                                                            LE.le.{0}
                                                              (Max.max.{0} epsLow
                                                                (HMul.hMul.{0, 0, 0} amax
                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                        (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                          (HMul.hMul.{0, 0, 0} kappa
                                                                            (∑ i,
                                                                              Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                  u_2, u_3}
                                                                                M e i))))
                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                        (HDiv.hDiv.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0} C lowCenter) lowLength)
                                                                          amin)
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} C lowLength) epsLow)))
                                                                    (HMul.hMul.{0, 0, 0} gaugeRatio epsLow))))
                                                              (1 / 2 : Real)) →
                                                            (have Clow :=
                                                                HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (HSub.hSub.{0, 0, 0} (1 : Real) d);
                                                              have Cmain :=
                                                                Max.max.{0} Clow
                                                                  (HMul.hMul.{0, 0, 0} amax
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                            (HMul.hMul.{0, 0, 0} kappa
                                                                              (∑ i,
                                                                                Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                    u_2, u_3}
                                                                                  M e i))))
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0} C lowLength) Clow)))
                                                                      (HMul.hMul.{0, 0, 0} gaugeRatio Clow)));
                                                              LE.le.{0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0} (4 : Real) Cmain)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HAdd.hAdd.{0, 0, 0} (1 : Real) R)
                                                                    (HAdd.hAdd.{0, 0, 0} rowError residual)))
                                                                (1 / 2 : Real)) →
                                                              ∀
                                                                (b :
                                                                  ↥(Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{u_1}
                                                                      H alphaA)),
                                                                LE.le.{0} (Norm.norm.{u_1} b)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} (8 : Real)
                                                                      (Max.max.{0}
                                                                        (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                          (HSub.hSub.{0, 0, 0} (1 : Real) d))
                                                                        (HMul.hMul.{0, 0, 0} amax
                                                                          (HAdd.hAdd.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                  (HMul.hMul.{0, 0, 0} kappa
                                                                                    (∑ i,
                                                                                      Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                          u_2, u_3}
                                                                                        M e i))))
                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                                (HMul.hMul.{0, 0, 0}
                                                                                  (HMul.hMul.{0, 0, 0} C lowLength)
                                                                                  (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                    (HSub.hSub.{0, 0, 0} (1 : Real)
                                                                                      d)))))
                                                                            (HMul.hMul.{0, 0, 0} gaugeRatio
                                                                              (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                (HSub.hSub.{0, 0, 0} (1 : Real) d)))))))
                                                                    (Norm.norm.{u_1}
                                                                      ((Erdos390.Full.PaperWeightedInverseExport.projectedRawLinearMap.{u_1}
                                                                          diagonalA kernelA H alphaA
                                                                          (ne_of_gt.{0}
                                                                            (id.{0}
                                                                              (id.{0}
                                                                                (Finset.sum_pos.{u_1, 0}
                                                                                  (fun i _hi =>
                                                                                    mul_pos.{0} (hH i)
                                                                                      (sq_pos_of_pos.{0} (hAlphaA i)))
                                                                                  Finset.univ_nonempty.{u_1})))))
                                                                        b))) := by
  exact @Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound
