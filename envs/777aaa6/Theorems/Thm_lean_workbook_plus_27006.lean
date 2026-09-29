-- Prove2me | Theorems.Thm_lean_workbook_plus_27006
-- name    : lean_workbook_plus_27006
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/df53c112-857e-4c1a-b588-2d88ac7ed848
-- statement:
--   Let $a,b,c > 0$ such that $a + b + c = 3$ . Prove that \n ${a^2} + {b^2} + {c^2} + a{b^2} + b{c^2} + c{a^2} \ge 6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27006 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3) : a^2 + b^2 + c^2 + a * b^2 + b * c^2 + c * a^2 ≥ 6   :=  by sorry
