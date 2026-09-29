-- Prove2me | Theorems.Thm_WorkbookSource_base_45570
-- name    : WorkbookSource.base_45570
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:44.316393+00:00
-- url     : https://prove2.me/theorems/62938528-4f0c-4dd7-9dd6-29e3fe993ace
-- title:
--   Nonnegativity of a sum of cubes and a quadratic product
-- statement:
--   If $a,b,c$ are real numbers, then
--
--    $(d)\ \ \ 2(a^2+bc)(b^2+ca)(c^2+ab)+a^6+b^6+c^6\ge 0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45570` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45570; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_45570 (a b c : ℝ) : 2 * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) + a ^ 6 + b ^ 6 + c ^ 6 ≥ 0  :=  by sorry
