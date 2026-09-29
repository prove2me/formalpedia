-- Prove2me | Theorems.Thm_lean_workbook_plus_42117
-- name    : lean_workbook_plus_42117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/69b25ed2-c469-4dfb-a840-51ce07e0cd60
-- statement:
--   Let $a,b,c$ be reals such that $b-c \geq a-b \geq 0$ . Show that \n $3(a^2b+b^2a+b^2c+c^2b+a^2c+c^2a) \geq 2(a^3+b^3+c^3)+12abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42117 (a b c : ℝ) (h : b - c ≥ a - b ∧ a - b ≥ 0) :
  3 * (a^2 * b + b^2 * a + b^2 * c + c^2 * b + a^2 * c + c^2 * a) ≥
    2 * (a^3 + b^3 + c^3) + 12 * a * b * c   :=  by sorry
