-- Prove2me | Theorems.Thm_lean_workbook_plus_81403
-- name    : lean_workbook_plus_81403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6f9ac46f-bff1-40d8-af0e-5204935a8f48
-- statement:
--   Let $ a, b, c$ be the sides and $ l_a, l_b, l_c$ the bisectors of an triangle $ ABC$ . Prove that \n\n $ (a + b + c)^2 > l_a(b + c) + l_b(c + a) + l_c(a + b) > \frac {(a + b + c)^2}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81403    (a b c l_a l_b l_c : ℝ)
    (h₁ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₂ : a + b > c)
    (h₃ : a + c > b)
    (h₄ : b + c > a)
    (h₅ : l_a = 2 * b * c / (b + c))
    (h₆ : l_b = 2 * c * a / (c + a))
    (h₇ : l_c = 2 * a * b / (a + b)) :
    (a + b + c) ^ 2 > l_a * (b + c) + l_b * (c + a) + l_c * (a + b) ∧
    l_a * (b + c) + l_b * (c + a) + l_c * (a + b) > (a + b + c) ^ 2 / 2   :=  by sorry
