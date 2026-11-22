-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:02:03.67235+00:00
-- url     : https://prove2.me/submissions/f320d329-fe89-40b4-81e3-77193bda9dc9

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
import Definitions.Def_erdos390_analytic_foundations_008

/- Source module: Erdos390.Full.PaperCanonicalBaseline -/
section


/-!
# Canonical barycentric baseline allocation

The active bridge first fixes positive head barycentric masses and then mixes
the two separated physical pools to hit the required logarithmic moment.
This file performs that construction exactly on the literal guarded finite
cells.  The resulting common cell-mass margin is an output.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open PaperBridgeFit ArithmeticModel

noncomputable section

variable {Head : Type*} [Fintype Head] [Nonempty Head]











namespace BarycentricTarget

variable {D : StructuredSampleData Head} (T : BarycentricTarget D)

































omit [Nonempty Head] in
/-- The physical logarithmic moment is exactly the selected target `mu`. -/
theorem physicalLogMoment :
    ∑ c : Cell Head,
        T.baseline.normalizedCellMass c * cellLogMean D c = T.mu := by
  let t := physicalMixingWeight D T.beta T.mu
  rw [Fintype.sum_prod_type]
  simp_rw [sum_physicalSign]
  simp only [T.baseline_normalizedCellMass, cellProbability]
  change (∑ h : Head,
      (T.beta h * (1 - t) * cellLogMean D (h, .minus) +
        T.beta h * t * cellLogMean D (h, .plus))) = T.mu
  rw [show
    (∑ h : Head,
      (T.beta h * (1 - t) * cellLogMean D (h, .minus) +
        T.beta h * t * cellLogMean D (h, .plus))) =
      (1 - t) * poolLogMean D T.beta .minus +
        t * poolLogMean D T.beta .plus by
      unfold poolLogMean
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      ring]
  have hden := T.denominator_pos.ne'
  dsimp [t, physicalMixingWeight]
  field_simp [hden]
  ring

end BarycentricTarget

end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetConnector -/
section


/-!
# The finite post-height baseline target

After the integer height `d` has been selected, the paper chooses a fresh
finite baseline.  Its total active mass is

`q_n = q0 - d`,

its unnormalized head-prime moments are the prescribed values
`A_p^act`, and its normalized logarithmic height above `n` is
`A(d) / q_n`.

In the repository, this last statistic is
`BridgeData.physicalScore = log (m/n)`.  The separately named
`BridgeData.ordinaryLogScore` is `log m`, so its unnormalized moment is
`A(d) + q_n L`, not `A(d)`.  Both identities are proved below.

The two-zero-cell rounding placement used to obtain the integer row quota
need not itself have barycentric product form.  Accordingly this module
does not identify that placement with the new baseline.  It instead uses
the paper's actual `HeadSimplexReserve`, `PhysicalInterpolationTarget`, and
`BridgeData.barycentricTargetOfPaperData` constructors to build a new
`BarycentricTarget`, and proves its finite moment identities directly.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## Literal post-height scalar data -/













/-! ## Genuine reserve and interpolation inputs -/



/-! ## Constructed paper data -/









/-! ## Exact mass and head moments -/





/-! ## Exact ordinary-log moment -/

/-- A uniform baseline allocation converts the sample physical-score sum
to the corresponding cell-log-mean sum. -/
theorem
    sum_baselineBaseWeight_mul_physicalScore_eq_cellLogMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (A : BaselineAllocation B.sampleData) :
    (∑ m : B.sampleData.Sample,
        A.baseWeight m * B.physicalScore m) =
      ∑ cell : Cell (PaperHeadSimplex.Tag P),
        A.cellMass cell * cellLogMean B.sampleData cell := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro cell _hcell
  simp only [BaselineAllocation.baseWeight, StructuredSampleData.cellOf,
    BridgeData.physicalScore, StructuredSampleData.value, cellLogMean]
  have hcard :
      (Fintype.card (B.sampleData.SampleAt cell) : Real) ≠ 0 := by
    exact_mod_cast
      Nat.ne_of_gt (B.sampleData.sampleAt_card_pos cell)
  change (∑ m : B.sampleData.SampleAt cell,
    (A.cellMass cell / (Fintype.card (B.sampleData.SampleAt cell) : ℝ)) *
      Real.log ((m.val : ℝ) / B.sampleData.n)) = _
  rw [← Finset.mul_sum]
  field_simp [hcard]

/-- A scaled barycentric seed has physical-score moment `q*T.mu`. -/
theorem
    sum_bankPaperCanonicalScaledActiveSeed_mul_physicalScore
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (T : BarycentricTarget B.sampleData) (q : Real) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          B.physicalScore m) =
      q * T.mu := by
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          B.physicalScore m) =
        q * ∑ m : B.sampleData.Sample,
          T.baseline.baseWeight m * B.physicalScore m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalScaledActiveSeed
      ring
    _ = q * ∑ cell : Cell (PaperHeadSimplex.Tag P),
        T.baseline.cellMass cell *
          cellLogMean B.sampleData cell := by
      rw [sum_baselineBaseWeight_mul_physicalScore_eq_cellLogMean]
    _ = q * ∑ cell : Cell (PaperHeadSimplex.Tag P),
        T.baseline.normalizedCellMass cell *
          cellLogMean B.sampleData cell := by
      apply congrArg (q * ·)
      apply Finset.sum_congr rfl
      intro cell _hcell
      unfold BaselineAllocation.normalizedCellMass
      rw [T.baseline_totalMass, div_one]
    _ = q * T.mu := by
      rw [T.physicalLogMoment]





/-- For the repository's literal `ordinaryLogScore = log m`, the
post-height seed has unnormalized moment
`A(d) + (q0-d)L`.  This is the exact conversion from the paper's height
above `n`; in the Section 8 ledger it equals `logY - Lambda0`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.ordinaryLogScore m) =
      bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d +
        bankPaperCanonicalSectionNinePostHeightActiveMass q0 d * B.L := by
  let Tpost :=
    bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H
  let qn := bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  have hq : qn ≠ 0 := ne_of_gt H.activeMass_pos
  have hphysical :
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H m *
            B.physicalScore m) =
        qn * Tpost.mu := by
    simpa only [Tpost, qn,
      bankPaperCanonicalSectionNinePostHeightActiveSeed] using
      (sum_bankPaperCanonicalScaledActiveSeed_mul_physicalScore
        B Tpost qn)
  have hmass :
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m) = qn := by
    simpa only [bankPaperCanonicalLiteralActiveMass, qn] using
      (bankPaperCanonicalSectionNinePostHeight_literalActiveMass_activeSeed
        B I hlo hhi H)
  have hpoint (m : B.sampleData.Sample) :
      B.ordinaryLogScore m = B.physicalScore m + B.L := by
    have hm : (B.sampleData.value m : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (B.sampleData.value_pos m)
    have hn : (B.sampleData.n : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one)
    unfold BridgeData.ordinaryLogScore BridgeData.physicalScore BridgeData.L
    rw [Real.log_div hm hn]
    ring
  have hmu :
      Tpost.mu =
        bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d / qn := by
    rfl
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.ordinaryLogScore m) =
        (∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H m *
            B.physicalScore m) +
          (∑ m : B.sampleData.Sample,
            bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H m) * B.L := by
      simp_rw [hpoint]
      calc
        (∑ m : B.sampleData.Sample,
            bankPaperCanonicalSectionNinePostHeightActiveSeed
                B I hlo hhi H m *
              (B.physicalScore m + B.L)) =
            ∑ m : B.sampleData.Sample,
              (bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H m *
                  B.physicalScore m +
                bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H m * B.L) := by
          apply Finset.sum_congr rfl
          intro m _hm
          ring
        _ =
            (∑ m : B.sampleData.Sample,
              bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H m *
                B.physicalScore m) +
              ∑ m : B.sampleData.Sample,
                bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H m * B.L := by
          rw [Finset.sum_add_distrib]
        _ =
            (∑ m : B.sampleData.Sample,
              bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H m *
                B.physicalScore m) +
              (∑ m : B.sampleData.Sample,
                bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H m) * B.L := by
          rw [Finset.sum_mul]
    _ = qn * Tpost.mu + qn * B.L := by
      rw [hphysical, hmass]
    _ = bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d +
        bankPaperCanonicalSectionNinePostHeightActiveMass q0 d * B.L := by
      rw [hmu]
      change
        qn *
              (bankPaperCanonicalSectionNinePostHeightActiveHeight
                B A0 d / qn) +
            qn * B.L =
          bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d +
            qn * B.L
      field_simp [hq]



/-! ## Combined finite target constructor -/



/-! ## Quantitative target margin -/









end

end Erdos390.WholePaper

end

universe u_1
theorem solution :
∀ {P : Finset.{0} Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals)
  (hlo :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      Eq.{1}
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B) sigma)
        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))))
  (hhi :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      Eq.{1}
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B) sigma)
        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))))
  {q0 A0 : Real} {d : Int} {exponent : Nat} {activeHeadTarget : ↥P → Real}
  (H :
    Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.{u_1} B I q0 A0 d exponent
      activeHeadTarget),
  Eq.{1}
    (∑ m,
      HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightActiveSeed.{u_1} B I hlo hhi H m)
        (Erdos390.Full.PaperBridgeFit.BridgeData.ordinaryLogScore.{0, u_1} B m))
    (HAdd.hAdd.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightActiveHeight.{u_1} B A0 d)
      (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
        (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, u_1} B))) := by
  exact @Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
