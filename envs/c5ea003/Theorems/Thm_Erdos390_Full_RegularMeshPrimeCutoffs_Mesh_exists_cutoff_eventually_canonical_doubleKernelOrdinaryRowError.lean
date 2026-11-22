-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:02:07.793248+00:00
-- url     : https://prove2.me/theorems/d621c033-51af-4f04-8b1b-65549cec02fe
-- title:
--   Mesh-independent cutoff for ordinary double-kernel quadrature
-- statement:
--   There are constants CRow>0 and W₀ such that, for every relative mesh M with δ>0, every W≥W₀ and every accuracy ε>0, all sufficiently large n admit W≠0, n>1 and scale separation for M,n,W, and each endpoint double-kernel error row obeys the bound below. CRow and W₀ are selected before the mesh; the eventual n-threshold may depend on it. This supplies the ordinary row error needed for arithmetic inversion.
--
--   $$\sum_j \operatorname{endpointDoubleKernelError}(M,n,W,i,j)\le \frac{C_{\rm Row}}{(\log W)^3}+\varepsilon.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/CanonicalEndpointDoubleKernelOrdinaryRowEventually.lean#L571-L752

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError :
∃ CRow,
  And (LT.lt.{0} (0 : Real) CRow)
    (∃ W₀,
      ∀ {δ ε : Real} (N : Erdos390.Full.RegularRelativeMesh.Mesh δ ε),
        LT.lt.{0} (0 : Real) δ →
          ∀ (W : Nat),
            LE.le.{0} W₀ W →
              ∀ (e : Real),
                LT.lt.{0} (0 : Real) e →
                  ∀ᶠ (n : Nat) in Filter.atTop.{0},
                    ∃ (_ : Ne.{1} W (0 : Nat)) (_ : LT.lt.{0} (1 : Nat) n) (_ :
                      Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation N n W),
                      ∀ (i : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount N) (1 : Nat))),
                        LE.le.{0} (∑ j, Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointDoubleKernelError N n W i j)
                          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} CRow (HPow.hPow.{0, 0, 0} (Real.log ↑W) (3 : Nat)))
                            e)) := by sorry
