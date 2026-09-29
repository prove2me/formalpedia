-- Prove2me | Theorems.Thm_lean_workbook_plus_21756
-- name    : lean_workbook_plus_21756
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/534cb84c-00f2-4b0f-a32e-645f4b8b7e75
-- statement:
--   $ y=q_1p^2c^2 \Rightarrow f(y)=q_1p^2f(c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21756 {q₁ p c : ℕ} (f : ℕ → ℕ) (y : ℕ) (h₁ : y = q₁ * (p ^ 2) * (c ^ 2)) :
  f y = f (q₁ * (p ^ 2) * (c ^ 2))   :=  by sorry
