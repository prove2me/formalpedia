-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalCenterEnvelopeCutoff_eventually_inverse
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:17:00.756612+00:00
-- url     : https://prove2.me/theorems/f62a7c5e-7a33-4a31-b173-cb4920edf522
-- title:
--   Uniform reciprocal-center envelope for the canonical partition
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Fix a regular relative mesh $M$ with $\delta>0$ and $W$ at least the source canonical center-envelope cutoff. For all sufficiently large $n$, every proof of $n>1$, $W\ne0$, and scale separation defines a canonical partition whose centers $\alpha_i$ satisfy
--
--   $$\frac1{\alpha_i}\le\frac4\delta\log L_n\qquad\text{for every band }i.$$
--
--   The cutoff is independent of the later mesh; only the eventual threshold depends on the mesh.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/CanonicalEndpointCenterEnvelopeEventually.lean#L113-L227

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCenterEnvelopeCutoff_eventually_inverse :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
  (W : Nat),
  LE.le.{0} Erdos390.Full.RegularMeshPrimeCutoffs.canonicalCenterEnvelopeCutoff W →
    ∀ᶠ (n : Nat) in Filter.atTop.{0},
      ∀ (hn : LT.lt.{0} (1 : Nat) n) (hWne : Ne.{1} W (0 : Nat))
        (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W)
        (i : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
        LE.le.{0}
          (HDiv.hDiv.{0, 0, 0} (1 : Real)
            (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0}
              (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S) i))
          (HMul.hMul.{0, 0, 0} (Erdos390.Full.RegularMeshPrimeCutoffs.canonicalCenterEnvelopeConstant delta)
            (Real.log (Erdos390.Full.Scale.L n))) := by sorry
