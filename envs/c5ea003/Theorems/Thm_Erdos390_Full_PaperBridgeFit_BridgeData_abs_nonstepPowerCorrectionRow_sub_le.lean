-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_nonstepPowerCorrectionRow_sub_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepPowerCorrectionRow_sub_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:12:26.257264+00:00
-- url     : https://prove2.me/theorems/2d57d2e7-6d4f-4958-a25a-042a20cc0f22
-- title:
--   Contraction of a weighted covariance-row difference against deviations
-- statement:
--   Let law₁ and law₂ be bounded valuation laws on finite spaces. Suppose w≥0 and every prime deviation of B has absolute value at most w. If p times the sum of absolute differences of the two prime-power covariance correction rows is at most ρ for every band prime p, then their non-step correction rows differ by at most ρw in every band i. The normalization is the literal harmonic band mass.
--
--   $$|(R_{\rm full}^{(1)}-R_{\rm sf}^{(1)})(i)-(R_{\rm full}^{(2)}-R_{\rm sf}^{(2)})(i)|\le\rho w.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperNonstepPowerCorrectionLedger.lean#L30-L176

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

universe u_1 u_2 u_3 u_4

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepPowerCorrectionRow_sub_le :
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
            (HMul.hMul.{0, 0, 0} rho w) := by sorry
