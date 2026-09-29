-- Prove2me | Theorems.Thm_lean_workbook_plus_72518
-- name    : lean_workbook_plus_72518
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/6785cd6b-daa8-4c65-bf7e-8879bd0361dc
-- statement:
--   Let $a_1, a_2,\cdots,a_n\ge 2$ $(n\ge 2)$. Prove that $\sqrt{a^2_1+(a_1+a_2)^2}+\sqrt{a^2_2+(a_2+a_3)^2}+\cdots+\sqrt{a^2_{n-1}+(a_{n-1}+a_n)^2}+\sqrt{a^2_n+(a_n+a_1)^2}\geq\sqrt{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72518 (n : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 2 ≤ a i) : 2 ≤ n → ∑ i in Finset.range n, Real.sqrt ((a i)^2 + (a i + a (i + 1))^2) ≥ Real.sqrt 5   :=  by sorry
