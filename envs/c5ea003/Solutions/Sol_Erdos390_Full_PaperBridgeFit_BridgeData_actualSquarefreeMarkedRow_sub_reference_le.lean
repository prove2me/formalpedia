-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeMarkedRow_sub_reference_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:14:34.473609+00:00
-- url     : https://prove2.me/submissions/9c20a856-5f83-45b8-8bfd-e7734b7b912a

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]















theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]











theorem covariance_sum_right (mu : FiniteProbability Omega)
    (F : Omega → ℝ) (s : Finset Iota) (G : Iota → Omega → ℝ) :
    mu.covariance F (fun omega ↦ ∑ i ∈ s, G i omega) =
      ∑ i ∈ s, mu.covariance F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_right]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_right, ih]



end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}













































end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperActualPrimePowerRelative -/
section


/-!
# Actual bridge specialization of the relative prime-power transfer

This file constructs the bounded valuation law directly from the genuine
guard-deleted tilted bridge sample.  It then applies the weighted row theorem
to the literal post-regression coefficients from Lemma 8.6.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75
open PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













/-- The primewise post-band score is the full-valuation score of the actual
bounded valuation law. -/
theorem postBandPrimeScore_eq_actualValuationSum [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (m : B.sampleData.Sample) :
    B.postBandPrimeScore q m =
      ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q p *
          (B.actualValuationLaw xi).V p m := by
  unfold postBandPrimeScore actualValuationLaw
    PrimePowerCovariance.BoundedValuationLaw.V
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ B.actualCompensatedNatCoefficient q p *
      valuation p (B.sampleData.value m))
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]





/-- Exact marked-row identification for the actual full and squarefree
post-band scores. -/
theorem actualMarkedRows_eq_covariances [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    fullMarkedRow (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) p =
      (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.postBandPrimeScore q) ∧
    squarefreeMarkedRow (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) p =
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q) := by
  constructor
  · unfold fullMarkedRow actualValuationLaw
      PrimePowerCovariance.BoundedValuationLaw.V
    congr 1
    funext m
    exact (B.postBandPrimeScore_eq_actualValuationSum xi q m).symm
  · rfl





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSquarefreeMarkedRow -/
section


/-!
# The squarefree marked row at the paper's relative scale

This file records the finite row calculation used in Lemma 8.6 and
Proposition 8.7.  A signed product-reciprocal comparison with the
Poisson--Dickman reference matrix is summed against the literal compensated
coefficient.  The result is pointwise in the marked prime and therefore does
not follow from a band-averaged operator estimate.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Exact finite expansion of the actual squarefree marked row. -/
theorem actualSquarefreeMarkedRow_eq_sum [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q) =
      ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          (B.actualValuationLaw xi).covII p r := by
  have hmarked := (B.actualMarkedRows_eq_covariances xi q p).2
  rw [← hmarked]
  unfold squarefreeMarkedRow covII
  rw [(B.actualValuationLaw xi).probability.covariance_sum_right]
  apply Finset.sum_congr rfl
  intro r hr
  rw [(B.actualValuationLaw xi).probability.covariance_smul_right]

/-- A product-reciprocal signed entry error gives a reciprocal marked-row
error.  This is the row analogue of the quadratic-form transfer, with the
diagonal first- and second-reciprocal terms kept separate. -/
theorem actualSquarefreeMarkedRow_sub_reference_le [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilonOff epsilonDiag epsilonSecond CL1 w : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hcoeffL1 :
      (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) ≤
          CL1 * w)
    (hentry : ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            epsilonDiag * (1 / (p : ℝ)) +
              epsilonSecond * (1 / (p : ℝ)) ^ 2
          else 0)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q) -
      ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          squarefreeReferenceEntry B.sampleData.n p r| ≤
      (epsilonOff * CL1 * w) * (1 / (p : ℝ)) +
        |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
  rw [B.actualSquarefreeMarkedRow_eq_sum xi q p]
  rw [← Finset.sum_sub_distrib]
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  calc
    |∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        (B.actualCompensatedNatCoefficient q r *
            (B.actualValuationLaw xi).covII p r -
          B.actualCompensatedNatCoefficient q r *
            squarefreeReferenceEntry B.sampleData.n p r)| =
      |∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          ((B.actualValuationLaw xi).covII p r -
            squarefreeReferenceEntry B.sampleData.n p r)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| *
          |(B.actualValuationLaw xi).covII p r -
            squarefreeReferenceEntry B.sampleData.n p r| := by
      calc
        _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r *
              ((B.actualValuationLaw xi).covII p r -
                squarefreeReferenceEntry B.sampleData.n p r)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [abs_mul]
    _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| *
          (epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
            if p = r then
              epsilonDiag * (1 / (p : ℝ)) +
                epsilonSecond * (1 / (p : ℝ)) ^ 2
            else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hentry p r hp hr) (abs_nonneg _)
    _ = epsilonOff * (1 / (p : ℝ)) *
          (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) +
        |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hoff :
          (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r| *
              (epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)))) =
          epsilonOff * (1 / (p : ℝ)) *
            (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
              |B.actualCompensatedNatCoefficient q r| *
                (1 / (r : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hoff]
      congr 1
      rw [Finset.sum_eq_single p]
      · simp
        ring
      · intro r hr hne
        simp [Ne.symm hne]
      · exact fun hnot ↦ (hnot hp).elim
    _ ≤ epsilonOff * (1 / (p : ℝ)) * (CL1 * w) +
        |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hcoeffL1
          (mul_nonneg hepsilonOff (one_div_nonneg.mpr hpR.le))) _
    _ = (epsilonOff * CL1 * w) * (1 / (p : ℝ)) +
        |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by ring









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
  {epsilonOff epsilonDiag epsilonSecond CL1 w : Real},
  LE.le.{0} (0 : Real) epsilonOff →
    LE.le.{0}
        (∑
          r ∈
            Erdos390.Full.ArithmeticModel.primeBand
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
          HMul.hMul.{0, 0, 0}
            (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedNatCoefficient.{u_1, u_2} B q r))
            (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑r))
        (HMul.hMul.{0, 0, 0} CL1 w) →
      (∀ (p r : Nat),
          Membership.mem.{0, 0}
              (Erdos390.Full.ArithmeticModel.primeBand
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
              p →
            Membership.mem.{0, 0}
                (Erdos390.Full.ArithmeticModel.primeBand
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                r →
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) p r)
                    (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      p r)))
                (HAdd.hAdd.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonOff (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                    (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑r))
                  (ite.{1} (Eq.{1} p r)
                    (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonDiag (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                      (HMul.hMul.{0, 0, 0} epsilonSecond
                        (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat))))
                    (0 : Real)))) →
        ∀ {p : Nat},
          Membership.mem.{0, 0}
              (Erdos390.Full.ArithmeticModel.primeBand
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
              p →
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.FiniteProbability.covariance.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                    (fun m =>
                      Erdos390.Full.ArithmeticModel.divInd p
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m))
                    (Erdos390.Full.PaperBridgeFit.BridgeData.postBandSquarefreeScore.{u_1, u_2} B q))
                  (∑
                    r ∈
                      Erdos390.Full.ArithmeticModel.primeBand
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                    HMul.hMul.{0, 0, 0}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedNatCoefficient.{u_1, u_2} B q r)
                      (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        p r))))
              (HAdd.hAdd.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonOff CL1) w)
                  (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                (HMul.hMul.{0, 0, 0}
                  (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedNatCoefficient.{u_1, u_2} B q p))
                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonDiag (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                    (HMul.hMul.{0, 0, 0} epsilonSecond
                      (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeMarkedRow_sub_reference_le
