-- Prove2me | solution 1 for Erdos390.Full.OmittedScoreCell.abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:03:28.502561+00:00
-- url     : https://prove2.me/submissions/20430743-caab-42fd-ae01-21c48022c7bc

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_OmittedScoreCell_abs_uniformCell_tilt_divInd_le_of_divisorScore_domination

/- Source module: Erdos390.Full.ArithmeticModel -/
section


/-!
# Arithmetic model for the full Erdős 390 formalization

This file connects the abstract covariance columns used by the earlier audit
companion to the actual arithmetic objects in the paper.  All definitions are
total, including at `n = 0`, `m = 0`, and at non-prime bases.  The valuation
identities themselves are stated with the mathematically necessary hypotheses
that the base is prime and the sampled integer is positive.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticModel















































theorem divInd_nonneg (d m : ℕ) : 0 ≤ divInd d m := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]























































end Erdos390.Full.ArithmeticModel

end

/- Source module: Erdos390.Full.UniformFiniteProbability -/
section


/-!
# Uniform probability on an actual finite cell

This is the exact bridge between counting averages on a finite arithmetic
cell and the `FiniteProbability` objects used by the tilt and covariance
modules.  Nonemptiness is explicit, so normalization never divides by a
silently vanishing cell cardinality.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Alpha : Type*}





/-- Expectation under the uniform law is the literal subtype sum divided by
the actual cell cardinality. -/
theorem uniformOnFinset_expect_eq (S : Finset Alpha) (hS : S.Nonempty)
    (F : S → ℝ) :
    (uniformOnFinset S hS).expect F =
      (∑ x : S, F x) / (S.card : ℝ) := by
  unfold expect
  calc
    (∑ x : S, (1 / (S.card : ℝ)) * F x) =
        (1 / (S.card : ℝ)) * ∑ x : S, F x := by
      rw [Finset.mul_sum]
    _ = (∑ x : S, F x) / (S.card : ℝ) := by ring

/-- Subtype summation is exactly the usual filtered finset summation. -/
theorem sum_subtype_eq_sum_filter (S : Finset Alpha) (F : Alpha → ℝ) :
    (∑ x : S, F x) = ∑ x ∈ S, F x := by
  exact Finset.sum_coe_sort S F

/-- Expectation written with the ambient function and the literal cell
cardinality. -/
theorem uniformOnFinset_expect_ambient_eq
    (S : Finset Alpha) (hS : S.Nonempty) (F : Alpha → ℝ) :
    (uniformOnFinset S hS).expect (fun x : S ↦ F x) =
      (∑ x ∈ S, F x) / (S.card : ℝ) := by
  rw [uniformOnFinset_expect_eq, sum_subtype_eq_sum_filter]

end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.OmittedScoreCell -/
section


/-!
# Omitted-score normalization on an actual arithmetic cell

This module composes the genuine uniform probability law of a finite cell
with the marked exponential-tilt inequality.  All expectations in the result
are literal counting averages over that same cell; there is no implicit
identification between a counting formula and an abstract probability law.
-/

namespace Erdos390.Full.OmittedScoreCell

open FiniteProbability DivisibilityMomentBounds

noncomputable section

/-- Counting average on a nonempty finite cell is exactly expectation under
its genuine uniform finite probability law. -/
theorem uniform_expect_eq_uniformAverage
    (S : Finset ℕ) (hS : S.Nonempty) (F : ℕ → ℝ) :
    (uniformOnFinset S hS).expect (fun m : S ↦ F m) =
      uniformAverage S F := by
  rw [uniformOnFinset_expect_ambient_eq]
  rfl







/-- Substitute explicit upper bounds for the unmarked and marked
divisor-score moments.  This is the final deterministic comparison needed
before inserting the common-multiple estimates. -/
theorem abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
    (S R : Finset ℕ) (hS : S.Nonempty) (D : ℕ)
    (score : ℕ → ℝ) {K beta totalBound markedBound : ℝ}
    (hbeta : 0 ≤ beta)
    (hdom : ∀ m ∈ S,
      |score m| ≤ beta * divisorScore R m)
    (hscore : ∀ m ∈ S, |score m| ≤ K)
    (htotalMoment :
      uniformAverage S (divisorScore R) ≤ totalBound)
    (hmarkedMoment : uniformAverage S
      (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m) ≤
        markedBound)
    (htotalBound : 0 ≤ totalBound)
    (hmarkedBound : 0 ≤ markedBound)
    (hsmall : Real.exp K * beta * totalBound < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) -
        uniformAverage S (ArithmeticModel.divInd D)| ≤
      (Real.exp K * beta * markedBound +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          (beta * totalBound)) /
        (1 - Real.exp K * beta * totalBound) := by
  have hactualSmall : Real.exp K * beta *
      uniformAverage S (divisorScore R) < 1 := by
    calc
      Real.exp K * beta * uniformAverage S (divisorScore R) ≤
          Real.exp K * beta * totalBound :=
        mul_le_mul_of_nonneg_left htotalMoment
          (mul_nonneg (Real.exp_pos K).le hbeta)
      _ < 1 := hsmall
  have hbase :=
    abs_uniformCell_tilt_divInd_le_of_divisorScore_domination
      S R hS D score hdom hscore hactualSmall
  let p := uniformAverage S (ArithmeticModel.divInd D)
  let Tactual := uniformAverage S (divisorScore R)
  let Bactual := uniformAverage S
    (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m)
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    rw [← uniform_expect_eq_uniformAverage S hS
      (ArithmeticModel.divInd D)]
    exact (uniformOnFinset S hS).expect_nonneg _ fun m ↦
      ArithmeticModel.divInd_nonneg D m
  have hTactual0 : 0 ≤ Tactual := by
    dsimp only [Tactual]
    rw [← uniform_expect_eq_uniformAverage S hS (divisorScore R)]
    exact (uniformOnFinset S hS).expect_nonneg _ fun m ↦ by
      unfold divisorScore
      exact Finset.sum_nonneg fun a ha ↦
        ArithmeticModel.divInd_nonneg a m
  have hBactual0 : 0 ≤ Bactual := by
    dsimp only [Bactual]
    rw [← uniform_expect_eq_uniformAverage S hS
      (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m)]
    exact (uniformOnFinset S hS).expect_nonneg _ fun m ↦
      mul_nonneg (ArithmeticModel.divInd_nonneg D m) (by
        unfold divisorScore
        exact Finset.sum_nonneg fun a ha ↦
          ArithmeticModel.divInd_nonneg a m)
  have hdenActual : 0 < 1 - Real.exp K * beta * Tactual := by
    dsimp only [Tactual]
    exact sub_pos.mpr hactualSmall
  have hdenBound : 0 < 1 - Real.exp K * beta * totalBound :=
    sub_pos.mpr hsmall
  have hnum :
      Real.exp K * beta * Bactual +
          Real.exp K * p * (beta * Tactual) ≤
        Real.exp K * beta * markedBound +
          Real.exp K * p * (beta * totalBound) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmarkedMoment
        (mul_nonneg (Real.exp_pos K).le hbeta))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htotalMoment hbeta)
        (mul_nonneg (Real.exp_pos K).le hp0))
  have htarget0 : 0 ≤
      Real.exp K * beta * markedBound +
        Real.exp K * p * (beta * totalBound) :=
    add_nonneg
      (mul_nonneg (mul_nonneg (Real.exp_pos K).le hbeta) hmarkedBound)
      (mul_nonneg (mul_nonneg (Real.exp_pos K).le hp0)
        (mul_nonneg hbeta htotalBound))
  have hbase' :
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) - p| ≤
        (Real.exp K * beta * Bactual +
          Real.exp K * p * (beta * Tactual)) /
          (1 - Real.exp K * beta * Tactual) := by
    simpa only [p, Tactual, Bactual] using hbase
  change |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) - p| ≤ _
  refine hbase'.trans ?_
  calc
    (Real.exp K * beta * Bactual +
        Real.exp K * p * (beta * Tactual)) /
        (1 - Real.exp K * beta * Tactual) ≤
      (Real.exp K * beta * markedBound +
        Real.exp K * p * (beta * totalBound)) /
        (1 - Real.exp K * beta * Tactual) :=
      div_le_div_of_nonneg_right hnum hdenActual.le
    _ ≤ (Real.exp K * beta * markedBound +
        Real.exp K * p * (beta * totalBound)) /
        (1 - Real.exp K * beta * totalBound) := by
      apply div_le_div_of_nonneg_left htarget0 hdenBound
      have hscaled : Real.exp K * beta * Tactual ≤
          Real.exp K * beta * totalBound :=
        mul_le_mul_of_nonneg_left htotalMoment
          (mul_nonneg (Real.exp_pos K).le hbeta)
      linarith
    _ = (Real.exp K * beta * markedBound +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          (beta * totalBound)) /
        (1 - Real.exp K * beta * totalBound) := by
      rfl

end

end Erdos390.Full.OmittedScoreCell

end

theorem solution :
∀ (S R : Finset.{0} Nat) (hS : Finset.Nonempty.{0} S) (D : Nat) (score : Nat → Real)
  {K beta totalBound markedBound : Real},
  LE.le.{0} (0 : Real) beta →
    (∀ (m : Nat),
        Membership.mem.{0, 0} S m →
          LE.le.{0} (abs.{0} (score m))
            (HMul.hMul.{0, 0, 0} beta (Erdos390.Full.DivisibilityMomentBounds.divisorScore R m))) →
      (∀ (m : Nat), Membership.mem.{0, 0} S m → LE.le.{0} (abs.{0} (score m)) K) →
        LE.le.{0}
            (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
              (Erdos390.Full.DivisibilityMomentBounds.divisorScore R))
            totalBound →
          LE.le.{0}
              (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S fun m =>
                HMul.hMul.{0, 0, 0} (Erdos390.Full.ArithmeticModel.divInd D m)
                  (Erdos390.Full.DivisibilityMomentBounds.divisorScore R m))
              markedBound →
            LE.le.{0} (0 : Real) totalBound →
              LE.le.{0} (0 : Real) markedBound →
                LT.lt.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta) totalBound) (1 : Real) →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.FiniteProbability.expect.{0}
                          (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                            (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun m => score ↑m)
                          fun m => Erdos390.Full.ArithmeticModel.divInd D ↑m)
                        (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                          (Erdos390.Full.ArithmeticModel.divInd D))))
                    (HDiv.hDiv.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta) markedBound)
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (Real.exp K)
                            (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                              (Erdos390.Full.ArithmeticModel.divInd D)))
                          (HMul.hMul.{0, 0, 0} beta totalBound)))
                      (HSub.hSub.{0, 0, 0} (1 : Real)
                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta) totalBound))) := by
  exact @Erdos390.Full.OmittedScoreCell.abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
