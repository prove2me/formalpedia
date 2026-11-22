-- Prove2me | solution 1 for Erdos390.Full.ContinuumCellGraph.IntervalMesh.abs_splitSharpEdge_cross_low_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:02:53.482135+00:00
-- url     : https://prove2.me/submissions/0d86ff87-26cb-415a-859f-f72b542664e1

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











end Anchor

/-- The product-kernel estimate gives the sharper edge bound needed for an
arbitrarily refined low block.  The usual bounded-quotient estimate only
gives `O(length j)`; here the additional factor `center j` is essential. -/
theorem sharpKernelEdge_le_productCenterLength_of_cell
    {C : ℝ}
    (hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j)
    (i j : Band) :
    M.sharpKernelEdge i j ≤ C * M.center j * M.length j := by
  have hi : 0 < M.center i := M.center_pos i
  have hj : 0 < M.center j := M.center_pos j
  have hcell := hCell i j
  have hedge := M.sharpKernelEdge_eq_normalizedKernelCell i j
  have hedgeAbs : M.sharpKernelEdge i j =
      |M.normalizedKernelCell i j| * (M.center j / M.center i) := by
    calc
      M.sharpKernelEdge i j = |M.sharpKernelEdge i j| :=
        (abs_of_nonneg (M.sharpKernelEdge_nonneg i j)).symm
      _ = |-M.normalizedKernelCell i j *
          (M.center j / M.center i)| := by rw [← hedge]
      _ = |M.normalizedKernelCell i j| *
          (M.center j / M.center i) := by
        rw [abs_mul, abs_neg, abs_of_pos (div_pos hj hi)]
  rw [hedgeAbs]
  calc
    |M.normalizedKernelCell i j| * (M.center j / M.center i) ≤
        (C * M.center i * M.length j) *
          (M.center j / M.center i) :=
      mul_le_mul_of_nonneg_right hcell (div_pos hj hi).le
    _ = C * M.center j * M.length j := by
      field_simp [ne_of_gt hi]



/-- Sum of all sharp edges from one output row into the low block. -/
theorem sum_splitSharpEdge_low_le
    (e : Sum Low High ≃ Band)
    {C lowCenter lowLength : ℝ}
    (hC : 0 ≤ C) (hLowCenterNonneg : 0 ≤ lowCenter)
    (hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j)
    (hLowCenter : ∀ l : Low, M.center (e (.inl l)) ≤ lowCenter)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (i : High) :
    ∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) ≤
      C * lowCenter * lowLength := by
  have hlengthNonneg : ∀ l : Low, 0 ≤ M.length (e (.inl l)) :=
    fun l ↦ (M.length_pos (e (.inl l))).le
  calc
    ∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) ≤
        ∑ l : Low,
          C * M.center (e (.inl l)) * M.length (e (.inl l)) := by
      apply Finset.sum_le_sum
      intro l hl
      exact M.sharpKernelEdge_le_productCenterLength_of_cell hCell
        (e (.inr i)) (e (.inl l))
    _ ≤ ∑ l : Low, C * lowCenter * M.length (e (.inl l)) := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hLowCenter l) hC)
        (hlengthNonneg l)
    _ = (C * lowCenter) *
        (∑ l : Low, M.length (e (.inl l))) := by
      rw [Finset.mul_sum]
    _ ≤ (C * lowCenter) * lowLength :=
      mul_le_mul_of_nonneg_left hLowLength
        (mul_nonneg hC hLowCenterNonneg)
    _ = C * lowCenter * lowLength := by ring

/-- Exact cross-row estimate from one high cell into all low cells.  The
first term uses the full raw supremum bound, while the second uses the
already established low-coordinate budget. -/
theorem abs_splitSharpEdge_cross_low_le
    (e : Sum Low High ≃ Band)
    {C lowCenter lowLength amin B lowBudget : ℝ}
    (hC : 0 ≤ C) (hLowCenterNonneg : 0 ≤ lowCenter)
    (hBNonneg : 0 ≤ B) (hLowBudgetNonneg : 0 ≤ lowBudget)
    (hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j)
    (hLowCenter : ∀ l : Low, M.center (e (.inl l)) ≤ lowCenter)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (hAmin : 0 < amin)
    (hHighCenter : ∀ i : High, amin ≤ M.center (e (.inr i)))
    (q : Sum Low High → ℝ)
    (hB : ∀ x, |M.center (e x) * q x| ≤ B)
    (hLowBudget : ∀ l : Low,
      |M.center (e (.inl l)) * q (.inl l)| ≤ lowBudget)
    (i : High) :
    |∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) *
        (q (.inr i) - q (.inl l))| ≤
      (C * lowCenter * lowLength) * B / amin +
        (C * lowLength) * lowBudget := by
  have hi : 0 < M.center (e (.inr i)) := M.center_pos _
  have hiLower : amin ≤ M.center (e (.inr i)) := hHighCenter i
  have hqi : |q (.inr i)| ≤ B / amin := by
    have hscaled : |q (.inr i)| ≤ B / M.center (e (.inr i)) := by
      apply (le_div_iff₀ hi).2
      rw [← abs_of_pos hi, ← abs_mul]
      simpa only [mul_comm] using hB (.inr i)
    exact hscaled.trans
      (div_le_div_of_nonneg_left hBNonneg hAmin hiLower)
  have hedgeNonneg (l : Low) :
      0 ≤ M.splitSharpEdge e (.inr i) (.inl l) :=
    M.sharpKernelEdge_nonneg _ _
  have hedgeBound (l : Low) :
      M.splitSharpEdge e (.inr i) (.inl l) ≤
        C * M.center (e (.inl l)) * M.length (e (.inl l)) :=
    M.sharpKernelEdge_le_productCenterLength_of_cell hCell _ _
  have hlowTerm (l : Low) :
      M.splitSharpEdge e (.inr i) (.inl l) * |q (.inl l)| ≤
        C * M.length (e (.inl l)) * lowBudget := by
    have hlength : 0 ≤ M.length (e (.inl l)) := (M.length_pos _).le
    have hcenter : 0 < M.center (e (.inl l)) := M.center_pos _
    calc
      M.splitSharpEdge e (.inr i) (.inl l) * |q (.inl l)| ≤
          (C * M.center (e (.inl l)) * M.length (e (.inl l))) *
            |q (.inl l)| :=
        mul_le_mul_of_nonneg_right (hedgeBound l) (abs_nonneg _)
      _ = C * M.length (e (.inl l)) *
          |M.center (e (.inl l)) * q (.inl l)| := by
        rw [abs_mul, abs_of_pos hcenter]
        ring
      _ ≤ C * M.length (e (.inl l)) * lowBudget :=
        mul_le_mul_of_nonneg_left (hLowBudget l)
          (mul_nonneg hC hlength)
  have hterm (l : Low) :
      |M.splitSharpEdge e (.inr i) (.inl l) *
          (q (.inr i) - q (.inl l))| ≤
        M.splitSharpEdge e (.inr i) (.inl l) * (B / amin) +
          C * M.length (e (.inl l)) * lowBudget := by
    rw [abs_mul, abs_of_nonneg (hedgeNonneg l)]
    calc
      M.splitSharpEdge e (.inr i) (.inl l) *
          |q (.inr i) - q (.inl l)| ≤
        M.splitSharpEdge e (.inr i) (.inl l) *
          (|q (.inr i)| + |q (.inl l)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (hedgeNonneg l)
      _ = M.splitSharpEdge e (.inr i) (.inl l) * |q (.inr i)| +
          M.splitSharpEdge e (.inr i) (.inl l) * |q (.inl l)| := by
        ring
      _ ≤ M.splitSharpEdge e (.inr i) (.inl l) * (B / amin) +
          C * M.length (e (.inl l)) * lowBudget :=
        add_le_add
          (mul_le_mul_of_nonneg_left hqi (hedgeNonneg l)) (hlowTerm l)
  have hedgeSum := M.sum_splitSharpEdge_low_le e hC hLowCenterNonneg
    hCell hLowCenter hLowLength i
  have hedgeSumNonneg :
      0 ≤ ∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) :=
    Finset.sum_nonneg fun l hl ↦ hedgeNonneg l
  calc
    |∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) *
        (q (.inr i) - q (.inl l))| ≤
      ∑ l : Low, |M.splitSharpEdge e (.inr i) (.inl l) *
        (q (.inr i) - q (.inl l))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Low,
        (M.splitSharpEdge e (.inr i) (.inl l) * (B / amin) +
          C * M.length (e (.inl l)) * lowBudget) :=
      Finset.sum_le_sum fun l hl ↦ hterm l
    _ = (∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l)) *
          (B / amin) +
        (C * (∑ l : Low, M.length (e (.inl l)))) * lowBudget := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.mul_sum]
    _ ≤ (C * lowCenter * lowLength) * (B / amin) +
        (C * lowLength) * lowBudget := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hedgeSum
          (div_nonneg hBNonneg hAmin.le)
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLowLength hC) hLowBudgetNonneg
    _ = (C * lowCenter * lowLength) * B / amin +
        (C * lowLength) * lowBudget := by ring

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

universe u_1 u_2 u_3
theorem solution :
∀ {Band : Type u_1} {Low : Type u_2} {High : Type u_3} [inst : Fintype.{u_1} Band] [inst_1 : Fintype.{u_2} Low]
  {epsilon : Real} (M : Erdos390.Full.ContinuumCellGraph.IntervalMesh.{u_1} epsilon Band)
  (e : Equiv.{max (u_3 + 1) (u_2 + 1), u_1 + 1} (Sum.{u_2, u_3} Low High) Band)
  {C lowCenter lowLength amin B lowBudget : Real},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) lowCenter →
      LE.le.{0} (0 : Real) B →
        LE.le.{0} (0 : Real) lowBudget →
          (∀ (i j : Band),
              LE.le.{0} (abs.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedKernelCell.{u_1} M i j))
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} C (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M i))
                  (Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M j))) →
            (∀ (l : Low),
                LE.le.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                  lowCenter) →
              LE.le.{0} (∑ l, Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                  lowLength →
                LT.lt.{0} (0 : Real) amin →
                  (∀ (i : High),
                      LE.le.{0} amin
                        (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))) →
                    ∀ (q : Sum.{u_2, u_3} Low High → Real),
                      (∀ (x : Sum.{u_2, u_3} Low High),
                          LE.le.{0}
                            (abs.{0}
                              (HMul.hMul.{0, 0, 0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e x))
                                (q x)))
                            B) →
                        (∀ (l : Low),
                            LE.le.{0}
                              (abs.{0}
                                (HMul.hMul.{0, 0, 0}
                                  (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M
                                    (e (Sum.inl.{u_2, u_3} l)))
                                  (q (Sum.inl.{u_2, u_3} l))))
                              lowBudget) →
                          ∀ (i : High),
                            LE.le.{0}
                              (abs.{0}
                                (∑ l,
                                  HMul.hMul.{0, 0, 0}
                                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitSharpEdge.{u_1, u_2, u_3} M e
                                      (Sum.inr.{u_2, u_3} i) (Sum.inl.{u_2, u_3} l))
                                    (HSub.hSub.{0, 0, 0} (q (Sum.inr.{u_2, u_3} i)) (q (Sum.inl.{u_2, u_3} l)))))
                              (HAdd.hAdd.{0, 0, 0}
                                (HDiv.hDiv.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C lowCenter) lowLength)
                                    B)
                                  amin)
                                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C lowLength) lowBudget)) := by
  exact @Erdos390.Full.ContinuumCellGraph.IntervalMesh.abs_splitSharpEdge_cross_low_le
