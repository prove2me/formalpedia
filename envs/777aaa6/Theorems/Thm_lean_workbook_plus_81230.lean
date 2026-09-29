-- Prove2me | Theorems.Thm_lean_workbook_plus_81230
-- name    : lean_workbook_plus_81230
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e57a0952-637a-4d30-92ff-08cf8abc9a62
-- statement:
--   Prove that $2(ab+bc+ca)\le2(a^2 +b^2 +c^2),$ for real numbers $a,b,c.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81230 (a b c: ℝ) : 2 * (a * b + b * c + c * a) ≤ 2 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
