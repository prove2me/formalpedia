-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceCenteringKernel_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:15:21.341903+00:00
-- url     : https://prove2.me/submissions/ee19042c-f983-442f-9b36-d7c0616d1bcc

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
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.PaperReferenceSharpPrimeGraph -/
section


/-!
# Prime-graph model for the literal sharp reference band operator

The endpoint double-quadrature route loses a factor depending on the first
cell width.  This file instead performs the comparison before band
quadrature.  A band coefficient `alpha_j x_j` is split exactly as

`t_p x_j + (alpha_j - t_p) x_j`.

The first term is a compression of the literal finite prime graph.  The
second is controlled by exact arithmetic centering.  Consequently the
constants below do not involve a least band centre, the number of bands, or
the low-cell width.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic FiniteGraphQuotientInverse
open ConditionedPoissonLimit DickmanBasic
open PoissonDickmanDirichlet
open PaperCanonicalSlowKappa

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- Exact first-moment identity on an actual arithmetic fiber. -/
theorem fiber_primeWeight_sum_eq_mass_mul_center (i : Band) :
    (∑ p ∈ B.partition.data.fiber i,
      primeWeight B.sampleData.n p) =
        B.harmonicMass i * B.bandCenter i := by
  change (∑ p ∈ B.partition.data.fiber i,
      tPrime B.sampleData.n p.1 / (p.1 : ℝ)) = _
  have h : (∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
        B.harmonicMass i * B.bandCenter i := by
    unfold harmonicMass bandCenter
    change (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.partition.data.mass i *
        ((∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
            B.partition.data.mass i)
    field_simp [ne_of_gt (B.partition.data.mass_pos i)]
  calc
    (∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 / (p.1 : ℝ)) =
        ∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = B.harmonicMass i * B.bandCenter i := h



















/-- The product bound for the Dickman kernel and the global arithmetic
deviation ledger give the remaining mesh-independent centering error. -/
theorem abs_referenceCenteringKernel_le
    {w CKernel R : ℝ} (hCKernel : 0 ≤ CKernel)
    (hR : 0 ≤ R)
    (hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (x : Band → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Band) :
    |B.referenceCenteringKernel x i| ≤ 7 * CKernel * w * R := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let A : ℝ := H * alpha
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by
    simpa only [alpha] using B.bandCenter_pos i
  have hA : 0 < A := mul_pos hH halpha
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |B.primeDeviation q * x (B.partition.band q) *
          covarianceKernel
            (tPrime B.sampleData.n p.1)
            (tPrime B.sampleData.n q.1) /
              ((p.1 : ℝ) * (q.1 : ℝ))|) ≤
        (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
          (CKernel * R * B.primeDeviationL1) := by
    calc
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
            (CKernel * R *
              ((1 / (q.1 : ℝ)) * |B.primeDeviation q|)) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [abs_div,
          abs_of_pos (mul_pos (hpPos p) (hpPos q)), abs_mul, abs_mul]
        have hK := hKernelFirst p q
        have hxq := hx (B.partition.band q)
        have hdev : 0 ≤ |B.primeDeviation q| := abs_nonneg _
        have hKnonneg : 0 ≤
            |covarianceKernel
              (tPrime B.sampleData.n p.1)
              (tPrime B.sampleData.n q.1)| := abs_nonneg _
        have hdx :
            |B.primeDeviation q| * |x (B.partition.band q)| ≤
              |B.primeDeviation q| * R :=
          mul_le_mul_of_nonneg_left hxq hdev
        have hbaseNonneg : 0 ≤ |B.primeDeviation q| * R :=
          mul_nonneg hdev hR
        have hfirst := mul_le_mul hdx hK hKnonneg hbaseNonneg
        exact (div_le_div_of_nonneg_right hfirst
          (mul_pos (hpPos p) (hpPos q)).le).trans_eq (by ring)
      _ = (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
          (CKernel * R * B.primeDeviationL1) := by
        unfold primeDeviationL1
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  unfold referenceCenteringKernel
  change |(1 / A) *
      (∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q * x (B.partition.band q) *
            covarianceKernel
              (tPrime B.sampleData.n p.1)
              (tPrime B.sampleData.n q.1) /
                ((p.1 : ℝ) * (q.1 : ℝ)))| ≤ _
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hA)]
  calc
    (1 / A) *
        |∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ))| ≤
      (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ))| := by
        apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hA.le)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun p hp ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
            (CKernel * R * B.primeDeviationL1) := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hA.le)
      exact Finset.sum_le_sum fun p hp ↦ hinner p
    _ = CKernel * R * B.primeDeviationL1 := by
      rw [← Finset.sum_mul]
      rw [show (∑ p ∈ B.partition.data.fiber i,
          tPrime B.sampleData.n p.1 / (p.1 : ℝ)) = A by
        simpa only [A] using B.fiber_primeWeight_sum_eq_mass_mul_center i]
      field_simp [ne_of_gt hA]
    _ ≤ CKernel * R * (7 * w) :=
      mul_le_mul_of_nonneg_left hdevL1 (mul_nonneg hCKernel hR)
    _ = 7 * CKernel * w * R := by ring







end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {w CKernel R : Real},
  LE.le.{0} (0 : Real) CKernel →
    LE.le.{0} (0 : Real) R →
      (∀
          (p q :
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
                  ↑p)
                (Erdos390.Full.ArithmeticModel.tPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  ↑q)))
            (HMul.hMul.{0, 0, 0} CKernel
              (Erdos390.Full.ArithmeticModel.tPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                ↑p))) →
        LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
            (HMul.hMul.{0, 0, 0} (7 : Real) w) →
          ∀ (x : Band → Real),
            (∀ (j : Band), LE.le.{0} (abs.{0} (x j)) R) →
              ∀ (i : Band),
                LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.referenceCenteringKernel.{u_1, u_2} B x i))
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (7 : Real) CKernel) w) R) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceCenteringKernel_le
