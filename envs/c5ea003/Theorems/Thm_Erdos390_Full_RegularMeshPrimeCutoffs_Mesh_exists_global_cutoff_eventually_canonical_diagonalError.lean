-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_exists_global_cutoff_eventually_canonical_diagonalError
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_global_cutoff_eventually_canonical_diagonalError
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:27:43.390007+00:00
-- url     : https://prove2.me/theorems/73480e34-0302-4480-b2e7-f0584550abc3
-- title:
--   Global cutoff for convergence of canonical normalized diagonals
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. There exists a natural cutoff $W_0$ such that for every regular relative mesh $M$ with parameter $\delta>0$, every $W\ge W_0$, and every $e>0$, all sufficiently large $n$ satisfy
--
--   $$\max_{0\le j\le M.\mathrm{cellCount}}|D^{\rm prime}_{n,W,j}-D^{\rm cont}_{n,W,j}|\le e.$$
--
--   The two quantities are the source normalized prime and continuum diagonal cell expressions on consecutive canonical endpoint cutoffs.
--
--   The cutoff is chosen before the mesh and accuracy; the eventual size threshold may depend on these later choices.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/CanonicalEndpointDiagonalEventually.lean#L142-L354

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.exists_global_cutoff_eventually_canonical_diagonalError :
∃ W₀,
  ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta),
    LT.lt.{0} (0 : Real) delta →
      ∀ (W : Nat),
        LE.le.{0} W₀ W →
          ∀ (e : Real),
            LT.lt.{0} (0 : Real) e →
              ∀ᶠ (n : Nat) in Filter.atTop.{0},
                ∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
                  LE.le.{0} (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointDiagonalError M n W j) e := by sorry
