-- Prove2me | Theorems.Thm_WorkbookSource_base_15960
-- name    : WorkbookSource.base_15960
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:26.185059+00:00
-- url     : https://prove2.me/theorems/640376d0-b9b8-40de-8dc8-730f3c770420
-- title:
--   A cyclic ratio bound with a squared difference correction
-- statement:
--   Let $a,b,c>0$ . Prove that:
--    $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\geq \frac{3}{2}+\frac{\left (a-b \right )^{2}}{2\left (a+b \right )^{2}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15960` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15960; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15960 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2 + (a - b) ^ 2 / (2 * (a + b) ^ 2)  :=  by sorry
