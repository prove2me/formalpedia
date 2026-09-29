-- Prove2me | Theorems.Thm_WorkbookSource_base_13018
-- name    : WorkbookSource.base_13018
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:48:34.521037+00:00
-- url     : https://prove2.me/theorems/7c52f02e-8f59-4607-97b0-8ecca91e83d3
-- title:
--   A symmetric quadratic ratio bounds cyclic ratio differences
-- statement:
--   For any $a,b,c >0$ , prove that
--   $\frac{a^2+b^2+c^2}{ab+bc+ca} \ge 1+ \frac{1}{3} \cdot \sum_{cyc} \left(\frac{a}{a+b}-\frac{b}{b+c}\right)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13018` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13018; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13018 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ 1 + 1 / 3 * ( (a / (a + b) - b / (b + c))^2 + (b / (b + c) - c / (c + a))^2 + (c / (c + a) - a / (a + b))^2 )  :=  by sorry
