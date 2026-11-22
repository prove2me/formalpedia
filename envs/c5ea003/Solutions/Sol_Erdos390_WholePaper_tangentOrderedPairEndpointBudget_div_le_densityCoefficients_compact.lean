-- Prove2me | solution 1 for Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_densityCoefficients_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:52:08.281484+00:00
-- url     : https://prove2.me/submissions/9afd817f-c362-4873-9677-ea53660e4a8e

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007
import Theorems.Thm_Erdos390_WholePaper_tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds_compact


section
universe u_1
theorem Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds : Erdos390.RemainingAnalyticGoal008_038.{u_1} := @Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds_compact
end
/- Source module: Erdos390.WholePaper.TangentPairArithmetic -/
section


/-!
# Finite arithmetic for tangent collision pairs

This file discharges the finite four-endpoint part of the
`hpairArithmetic` contract in `TangentSplitRequestLoads`.  It separates two
layers.

* Four per-equation bounds are assembled into the paper's one disjoint charge
  and two possible shared-label charges.  Distinct endpoints on the right
  request ensure that each left label can create at most one shared equation.
* A paper-scale specialization derives the per-equation bounds from a supplied
  effective list-density inequality

  `density * n <= lowerCard(request) * endpointLabel(request, side)`.

The specialization uses only `tangentBroadUpper n K h <= 2*n`, prime-label
positivity, and explicit hypotheses saying that every endpoint is at most a
cutoff whose first and second powers are at most `n`.  It yields the concrete
coefficients `12 / density^2` and `3 / density^2`.

No clean-list density estimate or cutoff asymptotic is proved here.  In a
paper application those are precisely the inputs needed to establish the
displayed effective-density and cutoff inequalities.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Coefficients and elementary endpoint budgets -/





/-- The disjoint-label density coefficient is nonnegative at nonnegative
density. -/
theorem tangentDensityDisjointCoefficient_nonneg
    {density : ℝ} (_hdensity : 0 ≤ density) :
    0 ≤ tangentDensityDisjointCoefficient density := by
  unfold tangentDensityDisjointCoefficient
  positivity



/-- The broad numerical endpoint never exceeds `2*n`. -/
theorem tangentBroadUpper_le_two_mul (n K h : ℕ) :
    tangentBroadUpper n K h ≤ 2 * n := by
  exact Nat.sub_le _ _

/-- Real form of the distinct-label endpoint-equation budget. -/
theorem cast_tangentEndpointEquationBudget_le_of_ne
    {N leftLabel rightLabel : ℕ} (hne : leftLabel ≠ rightLabel) :
    (tangentEndpointEquationBudget N leftLabel rightLabel : ℝ) ≤
      (N : ℝ) / ((leftLabel : ℝ) * rightLabel) + 1 := by
  rw [tangentEndpointEquationBudget, if_neg hne]
  calc
    ((N / (leftLabel * rightLabel) + 1 : ℕ) : ℝ) =
        ((N / (leftLabel * rightLabel) : ℕ) : ℝ) + 1 := by
      norm_num
    _ ≤ (N : ℝ) / (leftLabel * rightLabel : ℕ) + 1 := by
      exact add_le_add (Nat.cast_div_le (α := ℝ)) le_rfl
    _ = (N : ℝ) / ((leftLabel : ℝ) * rightLabel) + 1 := by
      norm_num

/-- Real form of the shared-label endpoint-equation budget. -/
theorem cast_tangentEndpointEquationBudget_le_of_eq
    (N label : ℕ) :
    (tangentEndpointEquationBudget N label label : ℝ) ≤
      (N : ℝ) / (label : ℝ) + 1 := by
  rw [tangentEndpointEquationBudget, if_pos rfl]
  calc
    ((N / label + 1 : ℕ) : ℝ) =
        ((N / label : ℕ) : ℝ) + 1 := by
      norm_num
    _ ≤ (N : ℝ) / (label : ℝ) + 1 := by
      exact add_le_add (Nat.cast_div_le (α := ℝ)) le_rfl

/-! ## Assembly of four endpoint equations -/





/-! ## Effective-density bounds for one endpoint equation -/

private theorem disjointEquation_density_crossBound
    {n N leftLabel rightLabel leftCard rightCard : ℕ}
    {density : ℝ}
    (hn : 0 < (n : ℝ)) (hdensity : 0 < density)
    (hleftPrime : leftLabel.Prime) (hrightPrime : rightLabel.Prime)
    (hne : leftLabel ≠ rightLabel)
    (hN : (N : ℝ) ≤ 2 * n)
    (hlabelProduct : (leftLabel : ℝ) * rightLabel ≤ n)
    (hleftScale : density * n ≤ (leftCard : ℝ) * leftLabel)
    (hrightScale : density * n ≤ (rightCard : ℝ) * rightLabel) :
    (n : ℝ) *
        (tangentEndpointEquationBudget N leftLabel rightLabel : ℝ) *
        density ^ 2 ≤
      3 * ((leftCard : ℝ) * rightCard) := by
  have hleftPos : 0 < (leftLabel : ℝ) := by
    exact_mod_cast hleftPrime.pos
  have hrightPos : 0 < (rightLabel : ℝ) := by
    exact_mod_cast hrightPrime.pos
  have hlabelProductPos :
      0 < (leftLabel : ℝ) * rightLabel :=
    mul_pos hleftPos hrightPos
  have hbudget := cast_tangentEndpointEquationBudget_le_of_ne
    (N := N) hne
  have hbudgetProduct :
      (tangentEndpointEquationBudget N leftLabel rightLabel : ℝ) *
          ((leftLabel : ℝ) * rightLabel) ≤
        (N : ℝ) + (leftLabel : ℝ) * rightLabel := by
    calc
      _ ≤ ((N : ℝ) / ((leftLabel : ℝ) * rightLabel) + 1) *
          ((leftLabel : ℝ) * rightLabel) :=
        mul_le_mul_of_nonneg_right hbudget hlabelProductPos.le
      _ = (N : ℝ) + (leftLabel : ℝ) * rightLabel := by
        field_simp [hleftPos.ne', hrightPos.ne']
  have hbudgetProductLe :
      (tangentEndpointEquationBudget N leftLabel rightLabel : ℝ) *
          ((leftLabel : ℝ) * rightLabel) ≤ 3 * n :=
    hbudgetProduct.trans (by linarith)
  have hscaleProduct :
      density ^ 2 * (n : ℝ) ^ 2 ≤
        ((leftCard : ℝ) * rightCard) *
          ((leftLabel : ℝ) * rightLabel) := by
    calc
      density ^ 2 * (n : ℝ) ^ 2 =
          (density * n) * (density * n) := by ring
      _ ≤ ((leftCard : ℝ) * leftLabel) *
          ((rightCard : ℝ) * rightLabel) :=
        mul_le_mul hleftScale hrightScale
          (mul_nonneg hdensity.le hn.le)
          (mul_nonneg (Nat.cast_nonneg leftCard) hleftPos.le)
      _ = ((leftCard : ℝ) * rightCard) *
          ((leftLabel : ℝ) * rightLabel) := by ring
  have hcombined :
      (tangentEndpointEquationBudget N leftLabel rightLabel : ℝ) *
          (density ^ 2 * (n : ℝ) ^ 2) ≤
        3 * ((leftCard : ℝ) * rightCard) * n := by
    calc
      _ ≤
          (tangentEndpointEquationBudget N leftLabel rightLabel : ℝ) *
            (((leftCard : ℝ) * rightCard) *
              ((leftLabel : ℝ) * rightLabel)) :=
        mul_le_mul_of_nonneg_left hscaleProduct (Nat.cast_nonneg _)
      _ = ((leftCard : ℝ) * rightCard) *
          ((tangentEndpointEquationBudget N leftLabel rightLabel : ℝ) *
            ((leftLabel : ℝ) * rightLabel)) := by ring
      _ ≤ ((leftCard : ℝ) * rightCard) * (3 * n) :=
        mul_le_mul_of_nonneg_left hbudgetProductLe (by positivity)
      _ = 3 * ((leftCard : ℝ) * rightCard) * n := by ring
  apply (mul_le_mul_iff_of_pos_left hn).mp
  convert hcombined using 1 <;> ring

private theorem sharedEquation_density_crossBound
    {n N label leftCard rightCard : ℕ} {density : ℝ}
    (hn : 0 < (n : ℝ)) (hdensity : 0 < density)
    (hlabelPrime : label.Prime)
    (hN : (N : ℝ) ≤ 2 * n)
    (hlabel : (label : ℝ) ≤ n)
    (hleftScale : density * n ≤ (leftCard : ℝ) * label)
    (hrightScale : density * n ≤ (rightCard : ℝ) * label) :
    (n : ℝ) * (tangentEndpointEquationBudget N label label : ℝ) *
        density ^ 2 ≤
      3 * label * ((leftCard : ℝ) * rightCard) := by
  have hlabelPos : 0 < (label : ℝ) := by
    exact_mod_cast hlabelPrime.pos
  have hbudget := cast_tangentEndpointEquationBudget_le_of_eq N label
  have hbudgetProduct :
      (tangentEndpointEquationBudget N label label : ℝ) * label ≤
        (N : ℝ) + label := by
    calc
      _ ≤ ((N : ℝ) / (label : ℝ) + 1) * label :=
        mul_le_mul_of_nonneg_right hbudget hlabelPos.le
      _ = (N : ℝ) + label := by
        field_simp [hlabelPos.ne']
  have hbudgetProductLe :
      (tangentEndpointEquationBudget N label label : ℝ) * label ≤
        3 * n := hbudgetProduct.trans (by linarith)
  have hscaleProduct :
      density ^ 2 * (n : ℝ) ^ 2 ≤
        ((leftCard : ℝ) * rightCard) * (label : ℝ) ^ 2 := by
    calc
      density ^ 2 * (n : ℝ) ^ 2 =
          (density * n) * (density * n) := by ring
      _ ≤ ((leftCard : ℝ) * label) *
          ((rightCard : ℝ) * label) :=
        mul_le_mul hleftScale hrightScale
          (mul_nonneg hdensity.le hn.le)
          (mul_nonneg (Nat.cast_nonneg leftCard) hlabelPos.le)
      _ = ((leftCard : ℝ) * rightCard) * (label : ℝ) ^ 2 := by
        ring
  have hcombined :
      (tangentEndpointEquationBudget N label label : ℝ) *
          (density ^ 2 * (n : ℝ) ^ 2) ≤
        3 * label * ((leftCard : ℝ) * rightCard) * n := by
    calc
      _ ≤ (tangentEndpointEquationBudget N label label : ℝ) *
          (((leftCard : ℝ) * rightCard) * (label : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hscaleProduct (Nat.cast_nonneg _)
      _ = ((leftCard : ℝ) * rightCard) * label *
          ((tangentEndpointEquationBudget N label label : ℝ) * label) := by
        ring
      _ ≤ ((leftCard : ℝ) * rightCard) * label * (3 * n) :=
        mul_le_mul_of_nonneg_left hbudgetProductLe (by positivity)
      _ = 3 * label * ((leftCard : ℝ) * rightCard) * n := by ring
  apply (mul_le_mul_iff_of_pos_left hn).mp
  convert hcombined using 1 <;> ring

/-! ## Paper-scale pair arithmetic -/



/-- The explicit effective list-density and cutoff bounds imply the complete
four-equation `hpairArithmetic` comparison.  Primality is used here only for
endpoint positivity; all counting has already been completed upstream. -/
theorem tangentOrderedPairEndpointBudget_div_le_densityCoefficients
    {Request : Type*} [DecidableEq Request]
    (n K h labelUpper : ℕ) (source target : Request → ℕ)
    (lowerCard : Request → ℕ) (density : ℝ)
    (hn : 0 < n) (hdensity : 0 < density)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hendpointDistinct : ∀ request, source request ≠ target request)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hlabelUpper : ∀ request side,
      tangentEndpointLabel source target side request ≤ labelUpper)
    (hlabelUpperLe : (labelUpper : ℝ) ≤ n)
    (hlabelUpperSq : (labelUpper : ℝ) ^ 2 ≤ n)
    (hlowerScale : ∀ request side,
      density * n ≤
        (lowerCard request : ℝ) *
          tangentEndpointLabel source target side request)
    (left right : Request) :
    (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
        source target left right : ℝ) /
        (lowerCard left * lowerCard right) ≤
      tangentDensityDisjointCoefficient density / n +
        (if tangentRequestHasLabel source target (source left) right
          then tangentDensitySharedCoefficient density * source left / n
          else 0) +
        (if tangentRequestHasLabel source target (target left) right
          then tangentDensitySharedCoefficient density * target left / n
          else 0) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hN : (tangentBroadUpper n K h : ℝ) ≤ 2 * n := by
    exact_mod_cast tangentBroadUpper_le_two_mul n K h
  let disjointCharge := tangentDensityDisjointCoefficient density / (n : ℝ)
  let sharedCharge : ℕ → ℝ := fun label ↦
    tangentDensitySharedCoefficient density * label / n
  apply tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds
    (tangentBroadUpper n K h) source target lowerCard
      disjointCharge sharedCharge hendpointDistinct
  intro leftRequest rightRequest leftSide rightSide
  let leftLabel := tangentEndpointLabel source target leftSide leftRequest
  let rightLabel := tangentEndpointLabel source target rightSide rightRequest
  have hleftPrime : leftLabel.Prime := hprime leftRequest leftSide
  have hrightPrime : rightLabel.Prime := hprime rightRequest rightSide
  have hleftUpper : leftLabel ≤ labelUpper :=
    hlabelUpper leftRequest leftSide
  have hrightUpper : rightLabel ≤ labelUpper :=
    hlabelUpper rightRequest rightSide
  have hleftUpperReal : (leftLabel : ℝ) ≤ labelUpper := by
    exact_mod_cast hleftUpper
  have hrightUpperReal : (rightLabel : ℝ) ≤ labelUpper := by
    exact_mod_cast hrightUpper
  have hleftScale := hlowerScale leftRequest leftSide
  have hrightScale := hlowerScale rightRequest rightSide
  have hdenominatorPos :
      0 < (lowerCard leftRequest : ℝ) * lowerCard rightRequest := by
    exact mul_pos (by exact_mod_cast (hlowerPos leftRequest))
      (by exact_mod_cast (hlowerPos rightRequest))
  by_cases heq : leftLabel = rightLabel
  · have hrightScale' :
        density * (n : ℝ) ≤
          (lowerCard rightRequest : ℝ) * leftLabel := by
      simpa only [heq] using hrightScale
    have hlabelLe : (leftLabel : ℝ) ≤ n :=
      hleftUpperReal.trans hlabelUpperLe
    have hcross := sharedEquation_density_crossBound hnReal hdensity
      hleftPrime hN hlabelLe hleftScale hrightScale'
    have hcoefficientPos : 0 < density ^ 2 := sq_pos_of_pos hdensity
    have hshared :
        (tangentEndpointEquationBudget (tangentBroadUpper n K h)
            leftLabel rightLabel : ℝ) /
            (lowerCard leftRequest * lowerCard rightRequest) ≤
          tangentDensitySharedCoefficient density * leftLabel / n := by
      rw [← heq]
      apply (div_le_div_iff₀ hdenominatorPos hnReal).2
      unfold tangentDensitySharedCoefficient
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply (le_div_iff₀ hcoefficientPos).2
      convert hcross using 1
      all_goals ring
    have hbaseNonneg : 0 ≤ disjointCharge / 4 := by
      dsimp only [disjointCharge]
      exact div_nonneg
        (div_nonneg (tangentDensityDisjointCoefficient_nonneg hdensity.le)
          (Nat.cast_nonneg n)) (by norm_num)
    simpa only [leftLabel, rightLabel, heq, if_pos,
      disjointCharge, sharedCharge] using
      hshared.trans (le_add_of_nonneg_left hbaseNonneg)
  · have hlabelProduct : (leftLabel : ℝ) * rightLabel ≤ n := by
      calc
        (leftLabel : ℝ) * rightLabel ≤
            (labelUpper : ℝ) * labelUpper :=
          mul_le_mul hleftUpperReal hrightUpperReal
            (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = (labelUpper : ℝ) ^ 2 := by ring
        _ ≤ n := hlabelUpperSq
    have hcross := disjointEquation_density_crossBound hnReal hdensity
      hleftPrime hrightPrime heq hN hlabelProduct hleftScale hrightScale
    have hcoefficientPos : 0 < density ^ 2 := sq_pos_of_pos hdensity
    have hdisjoint :
        (tangentEndpointEquationBudget (tangentBroadUpper n K h)
            leftLabel rightLabel : ℝ) /
            (lowerCard leftRequest * lowerCard rightRequest) ≤
          disjointCharge / 4 := by
      have hcharge : disjointCharge / 4 =
          3 / (density ^ 2 * n) := by
        dsimp only [disjointCharge, tangentDensityDisjointCoefficient]
        field_simp [hcoefficientPos.ne', hnReal.ne']
        all_goals ring
      rw [hcharge]
      apply (div_le_div_iff₀ hdenominatorPos
        (mul_pos hcoefficientPos hnReal)).2
      convert hcross using 1
      all_goals ring
    change _ ≤ disjointCharge / 4 +
      (if leftLabel = rightLabel then sharedCharge leftLabel else 0)
    rw [if_neg heq, add_zero]
    exact hdisjoint

/-! ## The literal `1/8` coefficient arithmetic -/





end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal008_039.{u_1} := by
  exact @Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_densityCoefficients
