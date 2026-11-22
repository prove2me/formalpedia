-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughCompactBV_translation_le_of_le
-- name    : Erdos390.WholePaper.roughCompactBV_translation_le_of_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:57:51.686582+00:00
-- url     : https://prove2.me/theorems/128db06a-a888-432f-a521-2508fd33218f
-- title:
--   Ordered compact bounded-variation translation estimate
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ have total variation at most $2$ on $[-5,5]$. For $0\le a\le b\le5$,
--   $$\int_0^5|f(a-v)-f(b-v)|\,dv\le2(b-a).$$
--   Only variation on the compact interval is needed. The estimate provides the translation input for the Saias correction analysis.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughCompactBVTranslation.lean#L34-L239

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.WholePaper.roughCompactBV_translation_le_of_le : Erdos390.RemainingAnalyticGoal008_019 := by sorry
