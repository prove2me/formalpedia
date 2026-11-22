-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_tendsto_low_endpointContinuumMass_div_log_y_cube_zero
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_low_endpointContinuumMass_div_log_y_cube_zero
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:28:36.131977+00:00
-- url     : https://prove2.me/theorems/79fc4ed4-6e67-43bc-ba97-0390a8eb6c5b
-- title:
--   Low-band continuum mass is negligible on the cubic logarithmic scale
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Let $M$ be a regular relative mesh with $\delta>0$ and let $W\ge2$. For its low band, let $a_n,b_n$ be the consecutive full endpoint cutoffs and put $m_n=\log\log b_n-\log\log a_n$. Then
--
--   $$\lim_{n\to\infty}\frac{m_n}{(\log y_n)^3}=0.$$
--
--   This controls the growth of the low continuum harmonic mass in estimates involving a reciprocal moving center.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/CanonicalEndpointDoubleKernelRowEventually.lean#L187-L278

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_low_endpointContinuumMass_div_log_y_cube_zero :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta),
  LT.lt.{0} (0 : Real) delta →
    ∀ {W : Nat},
      LE.le.{0} (2 : Nat) W →
        Filter.Tendsto.{0, 0}
          (fun n =>
            HDiv.hDiv.{0, 0, 0}
              (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.endpointContinuumMass M n W
                (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M))
              (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.ArithmeticModel.y n)) (3 : Nat)))
          Filter.atTop.{0} (nhds.{0} (0 : Real)) := by sorry
