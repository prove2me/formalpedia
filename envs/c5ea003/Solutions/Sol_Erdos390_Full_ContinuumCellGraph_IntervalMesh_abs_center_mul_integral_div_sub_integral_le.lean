-- Prove2me | solution 1 for Erdos390.Full.ContinuumCellGraph.IntervalMesh.abs_center_mul_integral_div_sub_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:58:16.95342+00:00
-- url     : https://prove2.me/submissions/35c05b4d-8581-4f1b-9c7c-1844a1958b5f

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















end IntervalMesh

end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.ContinuumRowResidualBound -/
section


/-!
# An explicit moving-low bound for the continuum row residual

Harmonic cell centers need not be close pointwise to the coordinate in the
moving low cell.  The correct cancellation is instead
`center * ∫ dt/t = ∫ dt`.  This file exploits that exact identity before
taking absolute values.  Consequently the residual is controlled by the
ordinary modulus of continuity of `F` and of the removable kernel on the
closed physical square, together with the omitted initial tail.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

theorem center_mul_harmonicMass (i : Band) :
    M.center i * M.harmonicMass i = M.length i := by
  unfold center
  field_simp [ne_of_gt (M.harmonicMass_pos i)]



/-- Harmonic and ordinary cell averages of a continuous function differ
only by its oscillation on that cell.  This remains uniform when the lower
endpoint tends to zero. -/
theorem abs_center_mul_integral_div_sub_integral_le
    (f : ℝ → ℝ) (hf : Continuous f) (i : Band)
    {rho : ℝ}
    (hosc : ∀ t ∈ Icc (M.lower i) (M.upper i),
      |f t - f (M.lower i)| ≤ rho) :
    |M.center i * (∫ t in M.lower i..M.upper i, f t / t) -
        ∫ t in M.lower i..M.upper i, f t| ≤
      2 * rho * M.length i := by
  let a := M.lower i
  let b := M.upper i
  let c := f a
  have ha : 0 < a := M.lower_pos i
  have hab : a ≤ b := le_of_lt (M.lower_lt_upper i)
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hdivInt : IntervalIntegrable (fun t : ℝ => f t / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact hf.continuousAt.div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  have hcdivInt : IntervalIntegrable (fun t : ℝ => c * (1 / t)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    simpa only [div_eq_mul_inv, one_mul] using
      (continuousAt_const.div continuousAt_id
        (ne_of_gt (ha.trans_le ht.1))).continuousWithinAt
  have hdiffDivInt : IntervalIntegrable
      (fun t : ℝ => (f t - c) / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact (hf.continuousAt.sub continuousAt_const).div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  have hmajorInt : IntervalIntegrable (fun t : ℝ => rho / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact continuousAt_const.div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  have hweighted :
      |∫ t in a..b, (f t - c) / t| ≤ rho * M.harmonicMass i := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ t in a..b, (f t - c) / t‖ ≤
          ∫ t in a..b, rho / t := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab _ hmajorInt
        filter_upwards with t ht
        have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
        have htpos : 0 < t := ha.trans_le htcc.1
        rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
        exact div_le_div_of_nonneg_right (hosc t htcc) htpos.le
      _ = rho * M.harmonicMass i := by
        unfold harmonicMass
        rw [show (fun t : ℝ => rho / t) =
            fun t : ℝ => rho * (1 / t) by
          funext t
          ring, intervalIntegral.integral_const_mul]
  have hordinary :
      |∫ t in a..b, f t - c| ≤ rho * M.length i := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := rho) (f := fun t : ℝ => f t - c)
      (fun t ht => by
        have htcc : t ∈ Icc a b := by
          have ht' : t ∈ uIcc a b := uIoc_subset_uIcc ht
          simpa only [uIcc_of_le hab] using ht'
        simpa only [Real.norm_eq_abs] using hosc t htcc)
    rw [Real.norm_eq_abs, abs_of_nonneg hba] at hnorm
    exact hnorm
  have hweightedDecomp :
      (∫ t in a..b, (f t - c) / t) =
        (∫ t in a..b, f t / t) - c * M.harmonicMass i := by
    rw [show (fun t : ℝ => (f t - c) / t) =
        fun t : ℝ => f t / t - c * (1 / t) by
      funext t
      ring]
    rw [intervalIntegral.integral_sub hdivInt hcdivInt,
      intervalIntegral.integral_const_mul]
    rfl
  have hfInt : IntervalIntegrable f volume a b := hf.intervalIntegrable _ _
  have hcInt : IntervalIntegrable (fun _t : ℝ => c) volume a b :=
    continuous_const.intervalIntegrable _ _
  have hordinaryDecomp :
      (∫ t in a..b, f t - c) =
        (∫ t in a..b, f t) - c * M.length i := by
    rw [intervalIntegral.integral_sub hfInt hcInt]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    unfold length
    ring
  have hidentity :
      M.center i * (∫ t in a..b, f t / t) -
          (∫ t in a..b, f t) =
        M.center i * (∫ t in a..b, (f t - c) / t) -
          (∫ t in a..b, f t - c) := by
    have hw : (∫ t in a..b, f t / t) =
        (∫ t in a..b, (f t - c) / t) + c * M.harmonicMass i := by
      linarith [hweightedDecomp]
    have ho : (∫ t in a..b, f t) =
        (∫ t in a..b, f t - c) + c * M.length i := by
      linarith [hordinaryDecomp]
    rw [hw, ho]
    calc
      M.center i *
            ((∫ t in a..b, (f t - c) / t) +
              c * M.harmonicMass i) -
          ((∫ t in a..b, f t - c) + c * M.length i) =
        (M.center i * (∫ t in a..b, (f t - c) / t) -
          (∫ t in a..b, f t - c)) +
          c * (M.center i * M.harmonicMass i - M.length i) := by ring
      _ = _ := by rw [M.center_mul_harmonicMass]; ring
  rw [hidentity]
  calc
    |M.center i * (∫ t in a..b, (f t - c) / t) -
        (∫ t in a..b, f t - c)| ≤
      |M.center i * (∫ t in a..b, (f t - c) / t)| +
        |∫ t in a..b, f t - c| := abs_sub _ _
    _ = M.center i * |∫ t in a..b, (f t - c) / t| +
        |∫ t in a..b, f t - c| := by
      rw [abs_mul, abs_of_pos (M.center_pos i)]
    _ ≤ M.center i * (rho * M.harmonicMass i) +
        rho * M.length i :=
      add_le_add
        (mul_le_mul_of_nonneg_left hweighted (M.center_pos i).le)
        hordinary
    _ = 2 * rho * M.length i := by
      rw [show M.center i * (rho * M.harmonicMass i) =
          rho * M.length i by
        rw [← mul_assoc, mul_comm (M.center i) rho, mul_assoc,
          M.center_mul_harmonicMass]]
      ring





























end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full

end

universe u_1
theorem solution :
∀ {Band : Type u_1} [inst : Fintype.{u_1} Band] {epsilon : Real}
  (M : Erdos390.Full.ContinuumCellGraph.IntervalMesh.{u_1} epsilon Band) (f : Real → Real),
  Continuous.{0, 0} f →
    ∀ (i : Band) {rho : Real},
      (∀ (t : Real),
          Membership.mem.{0, 0}
              (Set.Icc.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.lower.{u_1} M i)
                (Erdos390.Full.ContinuumCellGraph.IntervalMesh.upper.{u_1} M i))
              t →
            LE.le.{0}
              (abs.{0} (HSub.hSub.{0, 0, 0} (f t) (f (Erdos390.Full.ContinuumCellGraph.IntervalMesh.lower.{u_1} M i))))
              rho) →
        LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M i)
                (∫ (t : Real) in
                  Erdos390.Full.ContinuumCellGraph.IntervalMesh.lower.{u_1} M
                    i..Erdos390.Full.ContinuumCellGraph.IntervalMesh.upper.{u_1} M i,
                  HDiv.hDiv.{0, 0, 0} (f t) t))
              (∫ (t : Real) in
                Erdos390.Full.ContinuumCellGraph.IntervalMesh.lower.{u_1} M
                  i..Erdos390.Full.ContinuumCellGraph.IntervalMesh.upper.{u_1} M i,
                f t)))
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) rho)
            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M i)) := by
  exact @Erdos390.Full.ContinuumCellGraph.IntervalMesh.abs_center_mul_integral_div_sub_integral_le
