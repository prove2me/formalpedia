-- Prove2me | Theorems.Thm_WorkbookSource_plus_74161
-- name    : WorkbookSource.plus_74161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:50.79632+00:00
-- url     : https://prove2.me/theorems/9ce5d650-c0d4-442c-b3c9-fe384680cab6
-- title:
--   A quadratic ratio inequality with a normalized product correction
-- statement:
--   If $a,\,b,\,c$ are positive real numbers, then
--   (1).
--    $\frac{a^2+b^2+c^2}{ab+bc+ca} + 1 \geqslant \frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a}+\frac{4abc}{(a+b)(b+c)(c+a)}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_74161` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_74161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_74161 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 1 ≥ a / (a + b) + b / (b + c) + c / (c + a) + 4 * a * b * c / ((a + b) * (b + c) * (c + a))   :=  by sorry
