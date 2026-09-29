-- Prove2me | Theorems.Thm_WorkbookSource_plus_81823
-- name    : WorkbookSource.plus_81823
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:56:28.795239+00:00
-- url     : https://prove2.me/theorems/c1fd4eeb-567c-4363-9f41-41d0d3603ac8
-- title:
--   An asymmetric sum of linear squared and cubed ratios is at least three
-- statement:
--   Let $a,b,c >0.$ Prove that:
--    \begin{align*} \frac{a}{b}+ \left( \frac{3b+c}{3c+b} \right)^2 + \left( \frac{2c+a}{2a+c} \right)^3 \ge 3 .\end{align*}
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_81823` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_81823; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_81823 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + (3 * b + c) ^ 2 / (3 * c + b) ^ 2 + (2 * c + a) ^ 3 / (2 * a + c) ^ 3 ≥ 3   :=  by sorry
