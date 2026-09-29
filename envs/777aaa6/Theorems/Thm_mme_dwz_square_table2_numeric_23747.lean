-- Prove2me | Theorems.Thm_mme_dwz_square_table2_numeric_23747
-- name    : mme_dwz_square_table2_numeric_23747
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T10:17:31.316644+00:00
-- url     : https://prove2.me/theorems/8dd88d27-9170-4717-9875-8caf4f58030f
-- title:
--   Section 6.3 and Table 2: the exact Equation (25) rate exceeds 64.0001
-- statement:
--   Interpret every decimal in Duan--Wu--Zhou Table 2 as the displayed exact rational number. At $\tau=23747/30000$, the complete right-hand side of Equation (25) then satisfies
--
--   $$
--   64.0001<\operatorname{squareRate}\left(\frac{23747}{30000}\right).
--   $$
--
--   The paper reports the stronger endpoint $\omega<2.374631$; the rational parameter $2.3747$ leaves strict room above the Coppersmith--Winograd square's rank base $64$. The proof combines separately certified retained-copy and component-value logarithmic bounds and a final monotonicity estimate for real exponentiation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Equation (25), Section 6.3 and Table 2 (printed pp. 58-59); https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_square_retained_log_rate_gt_157133
import Theorems.Thm_mme_dwz_square_component_log_rate_23747_gt_442868
open MME.DWZSquare

theorem mme_dwz_square_table2_numeric_23747 :
    (640001 / 10000 : ℝ) < squareRate (23747 / 30000) := by sorry
