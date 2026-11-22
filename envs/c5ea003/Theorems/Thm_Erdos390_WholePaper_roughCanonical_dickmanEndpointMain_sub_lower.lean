-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughCanonical_dickmanEndpointMain_sub_lower
-- name    : Erdos390.WholePaper.roughCanonical_dickmanEndpointMain_sub_lower
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:55:40.584498+00:00
-- url     : https://prove2.me/theorems/b52c2202-98e8-47d9-8e82-3218a0278dec
-- title:
--   Lower growth of the Dickman endpoint main term
-- statement:
--   Let $0<A\le B$ and $y\ge2$ be natural numbers with $\log B\le5\log y$. Let $r_0$ be the positive canonical-pool Dickman floor. If $2/\log y\le r_0$, then
--   $$B\rho\!\left(\frac{\log B}{\log y}\right)-A\rho\!\left(\frac{\log A}{\log y}\right)\ge\frac{r_0}{2}(B-A).$$
--   The natural endpoints are kept intact, so the estimate can be used after floor losses have already been accounted for.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalRawBroadSurplusAsymptotic.lean#L77-L192

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007

theorem Erdos390.WholePaper.roughCanonical_dickmanEndpointMain_sub_lower : Erdos390.RemainingAnalyticGoal008_017 := by sorry
