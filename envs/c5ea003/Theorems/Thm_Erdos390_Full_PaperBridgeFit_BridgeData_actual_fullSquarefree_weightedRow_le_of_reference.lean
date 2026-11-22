-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actual_fullSquarefree_weightedRow_le_of_reference
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.actual_fullSquarefree_weightedRow_le_of_reference
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:13:14.834538+00:00
-- url     : https://prove2.me/theorems/6c0d272a-3491-42fc-b94a-37bceb625ab2
-- title:
--   Transfer of a weighted full-minus-squarefree row from a reference
-- statement:
--   For a valuation law $\lambda$, put $\Delta_\lambda(p,q)=\operatorname{Cov}_\lambda(v_p,v_q)-\operatorname{Cov}_\lambda(\mathbf1_{p\mid m},\mathbf1_{q\mid m})$. Let $B$ have nonempty head set and fix a tilt parameter and a bounded-valuation reference law. Suppose the reference satisfies $\mathrm{PrimePowerTransferBounds}$ with constants $C,\epsilon$, and for each band prime $p$ the actual/reference difference has weighted row at most $\rho$: $p\sum_q|\Delta_{\rm actual}(p,q)-\Delta_{\rm ref}(p,q)|\le\rho$. Then
--
--   $$p\sum_q|\Delta_{\rm actual}(p,q)|\le\frac CW+\epsilon+\rho.$$
--
--   The conclusion is on the literal prime subtype, suitable for both marked-prime and quadratic estimates.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualPrimePowerRowTransfer.lean#L35-L147

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

universe u_1 u_2 u_3

theorem Erdos390.Full.PaperBridgeFit.BridgeData.actual_fullSquarefree_weightedRow_le_of_reference :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  {OmegaRef : Type u_3} [inst_5 : Fintype.{u_3} OmegaRef] {MRef : Nat}
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (referenceLaw : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_3} OmegaRef MRef)
  {Cpow epsilon rhoPower : Real},
  Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_3} referenceLaw
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
      Cpow epsilon →
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
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q)
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q))
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_3} referenceLaw ↑p ↑q)
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_3} referenceLaw ↑p ↑q)))))
          rhoPower) →
      ∀
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
                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q)
                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q))))
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} Cpow
                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                  ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
              epsilon)
            rhoPower) := by sorry
