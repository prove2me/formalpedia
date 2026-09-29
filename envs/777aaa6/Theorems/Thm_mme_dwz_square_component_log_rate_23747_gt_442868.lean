-- Prove2me | Theorems.Thm_mme_dwz_square_component_log_rate_23747_gt_442868
-- name    : mme_dwz_square_component_log_rate_23747_gt_442868
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T09:49:19.281502+00:00
-- url     : https://prove2.me/theorems/b063af66-e1ab-4103-aa12-06ce4865eaf4
-- title:
--   DWZ Table 2: the component-value logarithmic rate exceeds 4.42868
-- statement:
--   For the exact $q=6$ component formulas and Table 2 weights, evaluate the component-value factor in Equation (25) at $\tau=23747/30000$. Its base-two logarithm satisfies
--
--   $$
--   R_{\mathrm{comp}}\left(\frac{23747}{30000}\right)>\frac{442868}{100000}=4.42868.
--   $$
--
--   This isolates the certified real-logarithm and real-power estimates for the five classes of level-two Coppersmith--Winograd constituents used in Section 6.3.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, the component-value formulas reused from Lemma 4.6 and specialized in Section 6.3, plus Table 2 (printed pp. 31-32 and 58-59); https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_dwz_square_data
open MME.DWZSquare

theorem mme_dwz_square_component_log_rate_23747_gt_442868 :
    (442868 / 100000 : ℝ) < componentLogRate (23747 / 30000) := by sorry
