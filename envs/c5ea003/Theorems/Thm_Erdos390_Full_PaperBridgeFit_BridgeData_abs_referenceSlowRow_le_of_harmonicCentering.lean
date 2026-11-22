-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_referenceSlowRow_le_of_harmonicCentering
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceSlowRow_le_of_harmonicCentering
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:10:54.25458+00:00
-- url     : https://prove2.me/theorems/b34d9c83-4f74-4039-8256-124ff377fd4c
-- title:
--   Reference slow-row bound from harmonic centering
-- statement:
--   For bridge data B, assume w≥0, CKernel≥0, |F(t_p)−1|≤CF t_p and |K(t_p,t_q)|≤CKernel t_pt_q on band primes. Suppose |dev_p|≤w and the deviation L¹ sum is at most 7w. Then the reference non-step slow row satisfies the following bound in every band i. No mesh or asymptotic hypothesis is needed.
--
--   $$|R_{\rm ref}(i)|\le(C_F+7C_{\rm Kernel})w\alpha_i.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperNonstepReferenceSlowDirect.lean#L32-L324

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

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceSlowRow_le_of_harmonicCentering :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {w CF CKernel : Real},
  LE.le.{0} (0 : Real) w →
    LE.le.{0} (0 : Real) CKernel →
      (∀
          (p :
            Erdos390.Full.ArithmeticBandGeometry.BandPrime
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
          LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0}
                (Erdos390.Full.DickmanBasic.F
                  (Erdos390.Full.ArithmeticModel.tPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    ↑p))
                (1 : Real)))
            (HMul.hMul.{0, 0, 0} CF
              (Erdos390.Full.ArithmeticModel.tPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                ↑p))) →
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
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} CKernel
                  (Erdos390.Full.ArithmeticModel.tPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    ↑p))
                (Erdos390.Full.ArithmeticModel.tPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  ↑q))) →
          (∀
              (p :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
              LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)) w) →
            LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
                (HMul.hMul.{0, 0, 0} (7 : Real) w) →
              ∀ (i : Band),
                LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.referenceSlowRow.{u_1, u_2} B i))
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} CF (HMul.hMul.{0, 0, 0} (7 : Real) CKernel)) w)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)) := by sorry
