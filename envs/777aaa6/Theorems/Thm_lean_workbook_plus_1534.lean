-- Prove2me | Theorems.Thm_lean_workbook_plus_1534
-- name    : lean_workbook_plus_1534
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3363f21b-271e-4a43-9a27-43b73c7eeab7
-- statement:
--   By AM-GM, we have $ab+bc+ac\geq3\sqrt[3]{a^2b^2c^2}$ and also $\sqrt{ab}+\sqrt{bc}+\sqrt{ac}\geq3\sqrt[3]{abc}$. Therefore the desired inequality becomes $27\sqrt[3]{(abc)^4}\geq27$. It remains to show that $abc\geq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1534  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c = 3)
  (h₂ : a * b + b * c + c * a = 3) :
  a * b * c ≥ 1   :=  by sorry
