-- Prove2me | Theorems.Thm_lean_workbook_plus_79039
-- name    : lean_workbook_plus_79039
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1d31f7ab-fe5d-41fd-aa09-2e1cd29ab36e
-- statement:
--   Given $a=p_1q_1+p_1^2$ and $b=p_1q_1+q_1^2$, show that $\sqrt{a+b}=p_1+q_1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79039 (a b p q : ℕ) : a = p * q + p ^ 2 ∧ b = p * q + q ^ 2 → √(a + b) = p + q   :=  by sorry
