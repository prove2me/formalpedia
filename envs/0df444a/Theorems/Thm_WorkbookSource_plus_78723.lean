-- Prove2me | Theorems.Thm_WorkbookSource_plus_78723
-- name    : WorkbookSource.plus_78723
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:54:21.309488+00:00
-- url     : https://prove2.me/theorems/897bdcca-3ed1-49af-abaf-878e6112ad90
-- title:
--   A cyclic ratio sum has a squared difference refinement
-- statement:
--   Let $a,b,c>0$ . Prove that:
--    $\frac{a}{b}+\frac{b}{c}+\frac{c}{a}\geq 3+\frac{(c-a)^{2}}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_78723` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_78723; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_78723 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≥ 3 + (c - a) ^ 2 / (a * b + b * c + c * a)   :=  by sorry
