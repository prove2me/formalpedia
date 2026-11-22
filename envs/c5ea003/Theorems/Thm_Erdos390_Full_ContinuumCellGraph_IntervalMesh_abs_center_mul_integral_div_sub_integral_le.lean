-- Prove2me | Theorems.Thm_Erdos390_Full_ContinuumCellGraph_IntervalMesh_abs_center_mul_integral_div_sub_integral_le
-- name    : Erdos390.Full.ContinuumCellGraph.IntervalMesh.abs_center_mul_integral_div_sub_integral_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:57:53.627594+00:00
-- url     : https://prove2.me/theorems/1efdc495-d5b4-4d02-8de8-6a5a1a11aef0
-- title:
--   Harmonic and ordinary cell averages differ by oscillation
-- statement:
--   Let an interval-mesh cell have endpoints $0<a<b$, length $\ell=b-a$, and harmonic center $c=\ell/\log(b/a)$. If $f$ is continuous and $|f(t)-f(a)|\le\rho$ on $[a,b]$, then
--
--   $$\left|c\int_a^b\frac{f(t)}t\,dt-\int_a^bf(t)\,dt\right|\le2\rho\ell.$$
--
--   The comparison stays uniform when the lower endpoint approaches zero.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/ContinuumRowResidualBound.lean#L56-L184

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1

theorem Erdos390.Full.ContinuumCellGraph.IntervalMesh.abs_center_mul_integral_div_sub_integral_le :
∀ {Band : Type u_1} [inst : Fintype.{u_1} Band] {epsilon : Real}
  (M : Erdos390.Full.ContinuumCellGraph.IntervalMesh.{u_1} epsilon Band) (f : Real → Real),
  Continuous.{0, 0} f →
    ∀ (i : Band) {rho : Real},
      (∀ (t : Real),
          Membership.mem.{0, 0}
              (Set.Icc.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.lower.{u_1} M i)
                (Erdos390.Full.ContinuumCellGraph.IntervalMesh.upper.{u_1} M i))
              t →
            LE.le.{0}
              (abs.{0} (HSub.hSub.{0, 0, 0} (f t) (f (Erdos390.Full.ContinuumCellGraph.IntervalMesh.lower.{u_1} M i))))
              rho) →
        LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M i)
                (∫ (t : Real) in
                  Erdos390.Full.ContinuumCellGraph.IntervalMesh.lower.{u_1} M
                    i..Erdos390.Full.ContinuumCellGraph.IntervalMesh.upper.{u_1} M i,
                  HDiv.hDiv.{0, 0, 0} (f t) t))
              (∫ (t : Real) in
                Erdos390.Full.ContinuumCellGraph.IntervalMesh.lower.{u_1} M
                  i..Erdos390.Full.ContinuumCellGraph.IntervalMesh.upper.{u_1} M i,
                f t)))
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) rho)
            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M i)) := by sorry
