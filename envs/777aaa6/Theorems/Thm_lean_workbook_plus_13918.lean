-- Prove2me | Theorems.Thm_lean_workbook_plus_13918
-- name    : lean_workbook_plus_13918
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/57942fa2-25e3-4662-b516-ab4036782791
-- statement:
--   Prove that for $a,b,c$ positive reals\n\n $a^2+b^2+c^2+ab+bc+ca \geq \sqrt{2(ab(a+b)+bc(b+c)+ca(c+a))(a+b+c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13918 :  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^2 + b^2 + c^2 + a * b + b * c + c * a ≥ Real.sqrt (2 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) * (a + b + c))   :=  by sorry
