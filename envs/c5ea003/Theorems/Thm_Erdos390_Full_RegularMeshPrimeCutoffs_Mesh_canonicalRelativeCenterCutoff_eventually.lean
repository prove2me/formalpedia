-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalRelativeCenterCutoff_eventually
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalRelativeCenterCutoff_eventually
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:50:03.03063+00:00
-- url     : https://prove2.me/theorems/7726f331-a02f-483e-8b54-9ef2016b3801
-- title:
--   Canonical arithmetic centers converge relatively after a global cutoff
-- statement:
--   Let $M$ be a regular relative mesh with $\delta>0$. Fix $W$ above the named global cutoff $\mathrm{canonicalRelativeCenterCutoff}$ and $e>0$. For all sufficiently large $n$ there are $W\ne0$, $n>1$, and a scale-separation certificate defining the canonical prime partition $P$ and endpoint certificate $E$, such that every cell satisfies
--
--   $$\left|\frac{P.\operatorname{center}(j)}{E.\operatorname{continuumCenter}(j)}-1\right|\le e.$$
--
--   The prime cutoff is selected independently of the mesh; only the eventual ambient threshold depends on that mesh.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/CanonicalEndpointRelativeCenterEventually.lean#L350-L444

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalRelativeCenterCutoff_eventually :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
  (W : Nat),
  LE.le.{0} Erdos390.Full.RegularMeshPrimeCutoffs.canonicalRelativeCenterCutoff W →
    ∀ (e : Real),
      LT.lt.{0} (0 : Real) e →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∃ (hWne : Ne.{1} W (0 : Nat)) (hn : LT.lt.{0} (1 : Nat) n) (S :
            Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W),
            have P := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S;
            have E := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta hn hWne S;
            ∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} P j)
                      (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.continuumCenter.{0} E j))
                    (1 : Real)))
                e := by sorry
