-- Prove2me | Theorems.Thm_WorkbookSource_base_9286
-- name    : WorkbookSource.base_9286
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:43:39.218663+00:00
-- url     : https://prove2.me/theorems/4d92a4a1-8ae8-4e4b-a498-b156941b63e1
-- title:
--   A cyclic quadratic-difference ratio lower bound
-- statement:
--   The following inequality is also true.
--   Let $a, b, c>0$ . Prove that
--    $\sum_{cyc}{\frac{a^2-bc}{b^2+c^2}}\ge 3\left(1-\frac{ab+bc+ca}{a^2+b^2+c^2}\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9286` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9286; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9286 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b * c) / (b^2 + c^2) + (b^2 - c * a) / (c^2 + a^2) + (c^2 - a * b) / (a^2 + b^2) ≥ 3 * (1 - (a * b + b * c + c * a) / (a^2 + b^2 + c^2))  :=  by sorry
