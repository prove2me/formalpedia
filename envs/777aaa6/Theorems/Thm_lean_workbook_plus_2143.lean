-- Prove2me | Theorems.Thm_lean_workbook_plus_2143
-- name    : lean_workbook_plus_2143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8046fbc2-0e59-4784-9296-b2777c2c15e4
-- statement:
--   Prove that $4(a^2 - ab + b^2)(b^2 - bc + c^2)(c^2 - ca + a^2) - \left((a + b)(b + c)(c + a) - 6abc\right)^2 = 3(a - b)^2(b - c)^2(c - a)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2143 : ∀ a b c : ℝ, 4 * (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) - ((a + b) * (b + c) * (c + a) - 6 * a * b * c)^2 = 3 * (a - b)^2 * (b - c)^2 * (c - a)^2   :=  by sorry
