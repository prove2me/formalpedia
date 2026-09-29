-- Prove2me | Theorems.Thm_lean_workbook_plus_29372
-- name    : lean_workbook_plus_29372
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4f75e5c0-57d0-4e26-82b3-340988cebb1c
-- statement:
--   Solution. We first note that, obviously, if two numbers are both rational then so are their product, sum and difference.\n\n$(+)\Rightarrow a+b-2\sqrt{ab}=(\sqrt{a}-\sqrt{b})^2\in\mathbb Q$\n\n$(\cdot)\Rightarrow (a-\sqrt{ab})(b-\sqrt{ab})=\sqrt{ab}(\sqrt{a}-\sqrt{b})^2\in\mathbb Q$\n\nFrom the two above statements, we deduce that $\sqrt{ab}\in\mathbb{Q}$ which, along with the initial relations, immediately gives that $a, b\in\mathbb Q$ , which is just the problem's conclusion.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29372  (a b : ℝ)
  (h₁ : ∃ x : ℚ, a = x)
  (h₂ : ∃ x : ℚ, b = x)
  (h₃ : ∃ x : ℚ, a + b = x)
  (h₄ : ∃ x : ℚ, a - b = x)
  (h₅ : ∃ x : ℚ, a * b = x) :
  ∃ x : ℚ, a = x ∧ ∃ x : ℚ, b = x   :=  by sorry
