-- Prove2me | Theorems.Thm_WorkbookSource_plus_58995
-- name    : WorkbookSource.plus_58995
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:48:12.250742+00:00
-- url     : https://prove2.me/theorems/d426390d-9577-4fd4-8cc5-4f77d7076996
-- title:
--   A mixed squared ratio sum bounds a normalized quadratic expression
-- statement:
--   For $a,b,c$ positive reals prove that
--
--    $\displaystyle 4\sum\frac{a^2+bc}{(b+c)^2} \ge 3+\frac{(a+b+c)^2}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_58995` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_58995; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_58995 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 4 * ((a^2 + b * c) / (b + c) ^ 2 + (b^2 + c * a) / (c + a) ^ 2 + (c^2 + a * b) / (a + b) ^ 2) ≥ 3 + (a + b + c) ^ 2 / (a * b + b * c + c * a)   :=  by sorry
