-- Prove2me | Theorems.Thm_Erdos390_WholePaper_bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
-- name    : Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:01:36.540835+00:00
-- url     : https://prove2.me/theorems/2625cacb-1395-4dc7-a271-c418c8f0eefe
-- title:
--   Ordinary logarithmic moment of the post-height active seed
-- statement:
--   Let $B$ be finite bridge data with head tags of a finite prime set $P$, and let physical intervals $I$ give exactly its sample lower and upper bounds. Fix real $q_0,A_0$, integer $d$, natural exponent and active head target satisfying the canonical post-height baseline-target inputs. Let $w_m$ be the resulting post-height active seed, $A(d)$ its canonical active height and $q(d)$ its canonical active mass. Then
--   $$\sum_m w_m\log(\mathrm{value}(m))=A(d)+q(d)B.L.$$
--   The sum runs over all structured samples.
--
--   This converts the height-above-$n$ normalization into the ordinary logarithmic moment used by Section 8.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNinePostHeightBaselineTargetConnector.lean#L418-L533

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

universe u_1

theorem Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment :
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
        (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, u_1} B))) := by sorry
