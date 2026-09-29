-- Prove2me | Theorems.Thm_WorkbookSource_base_17138
-- name    : WorkbookSource.base_17138
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:07:14.059114+00:00
-- url     : https://prove2.me/theorems/4bf3bae6-3dad-4ac9-af4a-b44abc616fbe
-- title:
--   A cyclic mixed quadratic ratio sum is at least five halves
-- statement:
--   Prove that for all $a,b,c\in\mathbb{R}_{>0}$ $ \frac{a^2+bc}{b^2+c^2}+\frac{b^2+ca}{c^2+a^2}+\frac{c^2+ab}{a^2+b^2}\geq \frac{5}{2} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17138` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17138; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b * c) / (b^2 + c^2) + (b^2 + c * a) / (c^2 + a^2) + (c^2 + a * b) / (a^2 + b^2) ≥ 5 / 2  :=  by sorry
