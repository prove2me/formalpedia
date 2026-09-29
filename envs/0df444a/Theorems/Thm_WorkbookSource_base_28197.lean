-- Prove2me | Theorems.Thm_WorkbookSource_base_28197
-- name    : WorkbookSource.base_28197
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:53:12.760454+00:00
-- url     : https://prove2.me/theorems/24ba1e6b-d480-4c47-8d10-e1e61d0e6ffa
-- title:
--   A cyclic mixed squared ratio sum is at least nine quarters
-- statement:
--   Prove this inequality with a,b,c are positive
--    $\frac{a^2+2bc}{(b+c)^2}+\frac{b^2+2ca}{(c+a)^2}+\frac{c^2+2ab}{(a+b)^2}\geq \frac{9}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28197` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28197; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28197 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + 2 * b * c) / (b + c) ^ 2 + (b^2 + 2 * c * a) / (c + a) ^ 2 + (c^2 + 2 * a * b) / (a + b) ^ 2 ≥ 9 / 4  :=  by sorry
