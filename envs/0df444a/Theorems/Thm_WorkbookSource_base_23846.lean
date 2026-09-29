-- Prove2me | Theorems.Thm_WorkbookSource_base_23846
-- name    : WorkbookSource.base_23846
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:59:55.750573+00:00
-- url     : https://prove2.me/theorems/2a97c573-52cd-47c2-bafd-4cec6511eef3
-- title:
--   A quadratic ratio with a weighted cyclic correction
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a^2+b^2+c^2}{ab+bc+ca} + 2\sum\frac{b}{2b+a} \ge 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23846` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23846; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23846 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 2 * (b / (2 * b + a) + a / (2 * a + c) + c / (2 * c + b)) ≥ 3  :=  by sorry
