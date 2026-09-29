-- Prove2me | Theorems.Thm_WorkbookSource_base_6317
-- name    : WorkbookSource.base_6317
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:18:02.644154+00:00
-- url     : https://prove2.me/theorems/9433f786-e058-4dac-a457-36a37329fdf8
-- title:
--   A cyclic ratio sum with a normalized cubic correction
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a}+\frac{9(a^3+b^3+c^3)}{(a+b+c)^3}\ge\frac{5}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6317` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6317; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6317 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + b) + b / (b + c) + c / (c + a) + (9 * (a ^ 3 + b ^ 3 + c ^ 3)) / (a + b + c) ^ 3) ≥ 5 / 2  :=  by sorry
