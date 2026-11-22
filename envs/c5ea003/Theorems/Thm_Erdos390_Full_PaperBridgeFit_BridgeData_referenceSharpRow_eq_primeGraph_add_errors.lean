-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_referenceSharpRow_eq_primeGraph_add_errors
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.referenceSharpRow_eq_primeGraph_add_errors
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:18:35.624396+00:00
-- url     : https://prove2.me/theorems/e3bdff26-0b8c-4810-a894-fb5e520d350c
-- title:
--   Exact decomposition of the reference sharp row into graph and errors
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Let $B$ be a bridge with finite head and band sets, and write $t_p=\log p/\log y_n$, $h_i$ for harmonic band masses, $\alpha_i$ for band centers, and $j(p)$ for the band of $p$. Let $R_{pr}$ be its squarefree Poisson–Dickman reference entry, $I_p=\mathbf1_{p\mid m}$, and $\mu_\xi$ its tilted law. For every real band vector $x$ and every band $i$, let $T^{\rm ref}x$ be the reference sharp row and let $G$ be the graph operator of the compressed prime graph. With the source row-residual error $E^{\rm res}$ and diagonal and kernel centering errors $E^{\rm diag},E^{\rm ker}$,
--
--   $$ (T^{\rm ref}x)_i=(Gx)_i+E_i^{\rm res}(x)+E_i^{\rm diag}(x)+E_i^{\rm ker}(x).$$
--
--   This exact identity separates graph coercivity from the three arithmetic approximation errors.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperReferenceSharpPrimeGraph.lean#L120-L390

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

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.referenceSharpRow_eq_primeGraph_add_errors :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) (x : Band → Real) (i : Band),
  Eq.{1}
    (Erdos390.Full.SquarefreeSharpBandTransfer.referenceSharpRow.{u_2}
      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) x i)
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0}
          (Erdos390.Full.FiniteGraphQuotientInverse.graphOperator.{u_2}
            (Erdos390.Full.PaperBridgeFit.BridgeData.compressedPrimeGraphEdge.{u_1, u_2} B) x i)
          (Erdos390.Full.PaperBridgeFit.BridgeData.referenceResidualError.{u_1, u_2} B x i))
        (Erdos390.Full.PaperBridgeFit.BridgeData.referenceCenteringDiagonal.{u_1, u_2} B x i))
      (Erdos390.Full.PaperBridgeFit.BridgeData.referenceCenteringKernel.{u_1, u_2} B x i)) := by sorry
