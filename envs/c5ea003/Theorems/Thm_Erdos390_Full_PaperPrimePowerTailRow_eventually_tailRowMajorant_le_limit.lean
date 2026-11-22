-- Prove2me | Theorems.Thm_Erdos390_Full_PaperPrimePowerTailRow_eventually_tailRowMajorant_le_limit
-- name    : Erdos390.Full.PaperPrimePowerTailRow.eventually_tailRowMajorant_le_limit
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:23:17.287779+00:00
-- url     : https://prove2.me/theorems/cb0d36e6-0129-4aa8-ba8b-44bc6b872fd0
-- title:
--   Real-power majorant for the residual tail row
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix $G\ge0$ and integer $W>1$. Put $T=G+G^2$, $c=\mathrm{cutoffScale}(W)$, and $H=\sum_{W<p\le Y}1/p$. The tail-row majorant is $T(cL/Y)(H+1)+T(cL)^2/Y^{2/3}+6G(cL)^2/Y^2$. Eventually in $n$,
--
--   $$\mathrm{tailRowMajorant}(G,W,n)\le13Tc\frac{L^2}{n^{1/5}}+Tc^2\frac{L^2}{n^{2/15}}+6Gc^2\frac{L^2}{n^{2/5}}.$$
--
--   The right-hand side is a sum of logarithmic squares divided by positive powers of $n$, making the vanishing residual row transparent.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperPrimePowerTailRow.lean#L450-L562

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

theorem Erdos390.Full.PaperPrimePowerTailRow.eventually_tailRowMajorant_le_limit :
∀ (G : Real) (W : Nat),
  LE.le.{0} (0 : Real) G →
    LT.lt.{0} (1 : Nat) W →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        LE.le.{0} (Erdos390.Full.PaperPrimePowerTailRow.tailRowMajorant G W n)
          (Erdos390.Full.PaperPrimePowerTailRow.tailRowLimitMajorant G W n) := by sorry
