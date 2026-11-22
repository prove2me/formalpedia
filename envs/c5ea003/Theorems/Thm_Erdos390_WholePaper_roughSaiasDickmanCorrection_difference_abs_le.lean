-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughSaiasDickmanCorrection_difference_abs_le
-- name    : Erdos390.WholePaper.roughSaiasDickmanCorrection_difference_abs_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:59:32.539709+00:00
-- url     : https://prove2.me/theorems/00a55a17-4ded-4491-a47b-f2ff865b167e
-- title:
--   Endpoint variation bound for the Saias–Dickman correction
-- statement:
--   Assume the source's compact bounded-variation translation principle. For natural $0<A\le B$, $y\ge2$, and $u(B,y)=\log B/\log y\le5$, let $E(X,y)$ denote the source's Saias–Dickman correction. Then
--   $$|E(B,y)-E(A,y)|\le\frac{5(B-A)}{\log y}.$$
--   This turns the compact translation estimate into an interval error bound for the correction term.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasNormalization.lean#L735-L838

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

theorem Erdos390.WholePaper.roughSaiasDickmanCorrection_difference_abs_le : Erdos390.RemainingAnalyticGoal008_026 := by sorry
