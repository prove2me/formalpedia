-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
-- name    : Erdos390.WholePaper.roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:01:07.656708+00:00
-- url     : https://prove2.me/theorems/775de1f1-2a0f-490c-a941-df8a32c97d22
-- title:
--   Inverse-log-square endpoint approximation from the normal-form defect
-- statement:
--   Let $C\ge0$ and $Y_0\in\mathbb N$. Suppose the reverse normal-form defect satisfies $|D(X,y,X)|\le CX/\log^2y$ whenever $y\ge Y_0$, $y\ge2$, $y<X$ and $\log X\le5\log y$. Let $Y_*=\max(Y_0,Y_{\rm contraction})$, where the latter is the canonical reciprocal-log prime contraction threshold. Then for all natural $X>0$ and $y\ge\max(2,Y_*)$ with $\log X\le5\log y$, the Saias endpoint error satisfies
--   $$|E(X,y)|\le\frac{10CX}{\log^2y}.$$
--
--   This produces the sharp endpoint envelope on all five constructed faces from the explicit defect bound.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasEndpointApproximation.lean#L300-L463

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_008

theorem Erdos390.WholePaper.roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect : Erdos390.RemainingAnalyticGoal008_029 := by sorry
