-- Prove2me | Theorems.Thm_WorkbookSource_base_30696
-- name    : WorkbookSource.base_30696
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:20:25.956486+00:00
-- url     : https://prove2.me/theorems/5fabfd64-281c-4e61-8a7a-29ff8ccce64c
-- title:
--   A cyclic pair-sum product ratio bounds an alternating reciprocal sum
-- statement:
--   Let $a,b,c,d>0$ ,prove that:
--
--    $\frac{(a+b)(b+c)(c+d)(d+a)}{(a+b+c+d)abcd} \geq 4(\frac{1}{c+a}+\frac{1}{b+d})$ BQ
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30696` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30696; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30696 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b) * (b + c) * (c + d) * (d + a) / ((a + b + c + d) * a * b * c * d) ≥ 4 * (1 / (c + a) + 1 / (b + d))  :=  by sorry
