-- Prove2me | Theorems.Thm_lean_workbook_plus_8013
-- name    : lean_workbook_plus_8013
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/5ebbaa05-32bc-4fc3-b017-e76c29a03bb9
-- statement:
--   prove that: \n$a^4+c^4+b^4+d^4 \geq 4abcd+2(a-b)(b-c)(c-d)(d-a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8013 : ∀ a b c d : ℝ, a^4 + b^4 + c^4 + d^4 ≥ 4 * a * b * c * d + 2 * (a - b) * (b - c) * (c - d) * (d - a)   :=  by sorry
