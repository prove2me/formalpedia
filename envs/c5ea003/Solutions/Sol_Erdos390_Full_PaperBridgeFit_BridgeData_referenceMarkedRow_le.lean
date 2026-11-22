-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.referenceMarkedRow_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:20:41.28521+00:00
-- url     : https://prove2.me/submissions/dc39165c-01f5-4bba-95da-af09e3a4f34f

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

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





/-- The Poisson--Dickman reference marked row is controlled by the same
pointwise and reciprocal-`L¹` ledgers as the literal compensated vector. -/
theorem referenceMarkedRow_le
    (q : B.RawBandGauge) {CF CKernel Csup CL1 w : ℝ}
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hcoeffSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ Csup * w)
    (hcoeffL1 :
      (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) ≤
          CL1 * w)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          squarefreeReferenceEntry B.sampleData.n p r| ≤
      (CKernel * CL1 + CF * Csup) * w * (1 / (p : ℝ)) := by
  let pp : BandPrime B.sampleData.n B.sampleData.W := ⟨p, hp⟩
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hentry : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |squarefreeReferenceEntry B.sampleData.n p r| ≤
        CKernel * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then CF * (1 / (p : ℝ)) else 0 := by
    intro r hr
    let rr : BandPrime B.sampleData.n B.sampleData.W := ⟨r, hr⟩
    have hrR : (0 : ℝ) < r := by
      exact_mod_cast (prime_of_mem_primeBand hr).pos
    by_cases hpr : p = r
    · subst r
      unfold squarefreeReferenceEntry squarefreeKernelEntry
      rw [if_pos rfl, if_pos rfl]
      calc
        |DickmanBasic.F (tPrime B.sampleData.n p) / (p : ℝ) +
            ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n p) (tPrime B.sampleData.n p) /
                ((p : ℝ) * (p : ℝ))| ≤
          |DickmanBasic.F (tPrime B.sampleData.n p) / (p : ℝ)| +
            |ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n p) (tPrime B.sampleData.n p) /
                ((p : ℝ) * (p : ℝ))| := abs_add_le _ _
        _ ≤ CF * (1 / (p : ℝ)) +
            CKernel * (1 / (p : ℝ)) * (1 / (p : ℝ)) := by
          rw [abs_div, abs_of_pos hpR, abs_div,
            abs_of_pos (mul_pos hpR hpR)]
          have hFp : |DickmanBasic.F (tPrime B.sampleData.n p)| ≤ CF :=
            hF pp
          have hKp : |ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
              CKernel := hKernel pp pp
          calc
            _ ≤ CF / (p : ℝ) + CKernel / ((p : ℝ) * (p : ℝ)) :=
              add_le_add
                (div_le_div_of_nonneg_right hFp hpR.le)
                (div_le_div_of_nonneg_right hKp
                  (mul_nonneg hpR.le hpR.le))
            _ = _ := by field_simp [hpR.ne']
        _ = CKernel * (1 / (p : ℝ)) * (1 / (p : ℝ)) +
            CF * (1 / (p : ℝ)) := by ring
    · unfold squarefreeReferenceEntry squarefreeKernelEntry
      rw [if_neg hpr, if_neg hpr, abs_div,
        abs_of_pos (mul_pos hpR hrR)]
      have hKr : |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n r)| ≤ CKernel :=
        hKernel pp rr
      calc
        _ ≤ CKernel / ((p : ℝ) * (r : ℝ)) :=
          div_le_div_of_nonneg_right hKr (mul_nonneg hpR.le hrR.le)
        _ = CKernel * (1 / (p : ℝ)) * (1 / (r : ℝ)) + 0 := by
          field_simp [hpR.ne', hrR.ne']
          ring
  calc
    |∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          squarefreeReferenceEntry B.sampleData.n p r| ≤
      ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| *
          |squarefreeReferenceEntry B.sampleData.n p r| := by
        calc
          _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
              |B.actualCompensatedNatCoefficient q r *
                squarefreeReferenceEntry B.sampleData.n p r| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [abs_mul]
    _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| *
          (CKernel * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
            if p = r then CF * (1 / (p : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hentry r hr) (abs_nonneg _)
    _ = CKernel * (1 / (p : ℝ)) *
          (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) +
        CF * (1 / (p : ℝ)) *
          |B.actualCompensatedNatCoefficient q p| := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hk :
          (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r| *
              (CKernel * (1 / (p : ℝ)) * (1 / (r : ℝ)))) =
          CKernel * (1 / (p : ℝ)) *
            (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
              |B.actualCompensatedNatCoefficient q r| *
                (1 / (r : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hk]
      congr 1
      rw [Finset.sum_eq_single p]
      · simp
        ring
      · intro r hr hne
        simp [Ne.symm hne]
      · exact fun hnot ↦ (hnot hp).elim
    _ ≤ CKernel * (1 / (p : ℝ)) * (CL1 * w) +
        CF * (1 / (p : ℝ)) * (Csup * w) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcoeffL1
          (mul_nonneg hCKernel (one_div_nonneg.mpr hpR.le)))
        (mul_le_mul_of_nonneg_left (hcoeffSup p hp)
          (mul_nonneg hCF (one_div_nonneg.mpr hpR.le)))
    _ = (CKernel * CL1 + CF * Csup) * w * (1 / (p : ℝ)) := by ring







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) {CF CKernel Csup CL1 w : Real},
  LE.le.{0} (0 : Real) CF →
    LE.le.{0} (0 : Real) CKernel →
      (∀ (r : Nat),
          Membership.mem.{0, 0}
              (Erdos390.Full.ArithmeticModel.primeBand
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
              r →
            LE.le.{0}
              (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedNatCoefficient.{u_1, u_2} B q r))
              (HMul.hMul.{0, 0, 0} Csup w)) →
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
          (∀
              (r :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
              LE.le.{0}
                (abs.{0}
                  (Erdos390.Full.DickmanBasic.F
                    (Erdos390.Full.ArithmeticModel.tPrime
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      ↑r)))
                CF) →
            (∀
                (r s :
                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                LE.le.{0}
                  (abs.{0}
                    (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                      (Erdos390.Full.ArithmeticModel.tPrime
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        ↑r)
                      (Erdos390.Full.ArithmeticModel.tPrime
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        ↑s)))
                  CKernel) →
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
                            p r)))
                    (HMul.hMul.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} CKernel CL1) (HMul.hMul.{0, 0, 0} CF Csup)) w)
                      (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.referenceMarkedRow_le
