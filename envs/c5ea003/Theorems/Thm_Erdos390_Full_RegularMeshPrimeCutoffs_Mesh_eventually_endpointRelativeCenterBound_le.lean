-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_eventually_endpointRelativeCenterBound_le
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.eventually_endpointRelativeCenterBound_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:26:36.707305+00:00
-- url     : https://prove2.me/theorems/84bc1a0b-16bd-4457-909d-74e3481dea52
-- title:
--   Eventual smallness of every canonical relative-center error
-- statement:
--   Fix a regular relative mesh $M$ with $\delta>0$, a natural cutoff $W$, real quadrature constants $C_m,C_t$, and $e>0$. For canonical endpoint cell $j$, denote its continuum mass and first moment by $m_j(n),t_j(n)$ and its prescribed mass and moment errors by $e_{m,j}(n),e_{t,j}(n)$. Then, simultaneously in all finitely many cells, eventually
--
--   $$m_j>0,\quad t_j>0,\quad e_{m,j}\le m_j/2,\quad 2e_{t,j}/t_j+2e_{m,j}/m_j\le e.$$
--
--   These explicit relative errors are the deterministic inputs for arithmetic-center convergence.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/CanonicalEndpointRelativeCenterEventually.lean#L246-L348

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.eventually_endpointRelativeCenterBound_le :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta),
  LT.lt.{0} (0 : Real) delta →
    ∀ {W : Nat} (Cmass Cmoment : Real) {e : Real},
      LT.lt.{0} (0 : Real) e →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
            And (LT.lt.{0} (0 : Real) (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointContinuumMass M n W j))
              (And (LT.lt.{0} (0 : Real) (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointContinuumMoment M n W j))
                (And
                  (LE.le.{0} (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointMassError M Cmass n W j)
                    (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointContinuumMass M n W j)
                      (2 : Real)))
                  (LE.le.{0}
                    (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointRelativeCenterBound M Cmass Cmoment n W j) e))) := by sorry
