-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepPowerCorrectionRow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:15:14.112195+00:00
-- url     : https://prove2.me/submissions/73af4905-d73b-46f3-92c4-6f840aee98b6

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.PaperNonstepPowerCorrectionLedger -/
section


/-!
# Exact non-step aggregation of a power-correction row

The guard/physical comparison is naturally stated as
`p * sum_q |Delta_{pq}| <= rho`.  Contracting it against the literal
primewise coefficient `g_q` costs only `sup |g_q|`; averaging over the
output fiber then uses its exact harmonic mass.  No output centre is divided
out in this finite lemma.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

set_option maxHeartbeats 1000000

/-- A reciprocal weighted covariance-row comparison contracts against the
literal non-step coefficient with the exact bound `rho * w`. -/
theorem abs_nonstepPowerCorrectionRow_sub_le
    {Omega₁ Omega₂ : Type*} [Fintype Omega₁] [Fintype Omega₂]
    {M₁ M₂ : ℕ}
    (law₁ : BoundedValuationLaw Omega₁ M₁)
    (law₂ : BoundedValuationLaw Omega₂ M₂)
    {rho w : ℝ} (hw : 0 ≤ w)
    (hdevSup : ∀ q : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation q| ≤ w)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(law₁.covVV p.1 q.1 - law₁.covII p.1 q.1) -
            (law₂.covVV p.1 q.1 - law₂.covII p.1 q.1)| ≤ rho)
    (i : Band) :
    |(B.nonstepFullCoefficientRow law₁ i -
          B.nonstepSquarefreeCoefficientRow law₁ i) -
        (B.nonstepFullCoefficientRow law₂ i -
          B.nonstepSquarefreeCoefficientRow law₂ i)| ≤
      rho * w := by
  let H : ℝ := B.harmonicMass i
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  let D := fun (p q : BandPrime B.sampleData.n B.sampleData.W) ↦
    (law₁.covVV p.1 q.1 - law₁.covII p.1 q.1) -
      (law₂.covVV p.1 q.1 - law₂.covII p.1 q.1)
  have hrho : 0 ≤ rho := by
    obtain ⟨p, hp⟩ := B.partition.fiber_nonempty i
    let p' : BandPrime B.sampleData.n B.sampleData.W := p
    have hnonneg : 0 ≤ (p'.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W, |D p' q| := by
      exact mul_nonneg (hpPos p').le (Finset.sum_nonneg fun q _hq ↦ abs_nonneg _)
    exact hnonneg.trans (by simpa only [D] using hrow p')
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      |∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q * D p q| ≤
        (rho * w) * (1 / (p.1 : ℝ)) := by
    have hsum :
        ∑ q : BandPrime B.sampleData.n B.sampleData.W, |D p q| ≤
          rho / (p.1 : ℝ) := by
      exact (le_div_iff₀ (hpPos p)).2 (by
        simpa only [D, mul_comm] using hrow p)
    calc
      |∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q * D p q| ≤
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation q * D p q| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation q| * |D p q| := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [abs_mul]
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          w * |D p q| := by
        apply Finset.sum_le_sum
        intro q _hq
        exact mul_le_mul_of_nonneg_right (hdevSup q) (abs_nonneg _)
      _ = w * ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |D p q| := by rw [Finset.mul_sum]
      _ ≤ w * (rho / (p.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hw
      _ = (rho * w) * (1 / (p.1 : ℝ)) := by ring
  have hmass : (1 / H) *
      ∑ p ∈ B.partition.data.fiber i, (1 / (p.1 : ℝ)) = 1 := by
    change (1 / H) * H = 1
    field_simp [hH.ne']
  unfold nonstepFullCoefficientRow nonstepSquarefreeCoefficientRow
  have hrewrite :
      (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (((∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law₁.covVV p.1 q.1) -
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law₁.covII p.1 q.1) -
            ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law₂.covVV p.1 q.1) -
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law₂.covII p.1 q.1)) =
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * D p q := by
    congr 1
    apply Finset.sum_congr rfl
    intro p _hp
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    dsimp only [D]
    ring
  have hrowRewrite :
      ((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₁.covVV p.1 q.1 -
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₁.covII p.1 q.1) -
      ((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₂.covVV p.1 q.1 -
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law₂.covII p.1 q.1) =
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * D p q := by
    rw [← hrewrite]
    dsimp only [H]
    simp_rw [Finset.sum_sub_distrib]
    ring
  rw [hrowRewrite]
  calc
    |(1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * D p q| ≤
      (1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          |∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * D p q| := by
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hH)]
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          (rho * w) * (1 / (p.1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun p _hp ↦ hinner p
    _ = rho * w := by
      rw [← Finset.mul_sum]
      calc
        (1 / H) * ((rho * w) *
            ∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ))) =
          (rho * w) * ((1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ))) := by ring
        _ = rho * w := by rw [hmass, mul_one]

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2 u_3 u_4
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {Omega₁ : Type u_3} {Omega₂ : Type u_4}
  [inst_4 : Fintype.{u_3} Omega₁] [inst_5 : Fintype.{u_4} Omega₂] {M₁ M₂ : Nat}
  (law₁ : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_3} Omega₁ M₁)
  (law₂ : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_4} Omega₂ M₂) {rho w : Real},
  LE.le.{0} (0 : Real) w →
    (∀
        (q :
          Erdos390.Full.ArithmeticBandGeometry.BandPrime
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
        LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B q)) w) →
      (∀
          (p :
            Erdos390.Full.ArithmeticBandGeometry.BandPrime
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
          LE.le.{0}
            (HMul.hMul.{0, 0, 0} (↑↑p)
              (∑ q :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_3} law₁ ↑p ↑q)
                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_3} law₁ ↑p ↑q))
                    (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_4} law₂ ↑p ↑q)
                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_4} law₂ ↑p ↑q)))))
            rho) →
        ∀ (i : Band),
          LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepFullCoefficientRow.{u_1, u_2, u_3} B law₁ i)
                  (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepSquarefreeCoefficientRow.{u_1, u_2, u_3} B law₁ i))
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepFullCoefficientRow.{u_1, u_2, u_4} B law₂ i)
                  (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepSquarefreeCoefficientRow.{u_1, u_2, u_4} B law₂ i))))
            (HMul.hMul.{0, 0, 0} rho w) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepPowerCorrectionRow_sub_le
