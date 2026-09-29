-- Prove2me | Theorems.Thm_lean_workbook_plus_34486
-- name    : lean_workbook_plus_34486
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f7873398-5324-4fdd-af31-b7d09c193a77
-- statement:
--   Is there a function $f:\mathbb R \to \mathbb R$ such that: \n\n $f(x)=0 \iff x=0$ \n\n $\forall x\in \mathbb R:f(x)+f(2x)+f(3x)+...+f(nx)=0 :P(x)$ where $n\ge 2$ is a fixed natural number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34486 (n : ℕ) (hn : 2 ≤ n) : ∃ f : ℝ → ℝ, (∀ x, ∑ i in Finset.range n, f (i * x) = 0 ↔ x = 0) ∧ (∀ x, f x = 0 ↔ x = 0)   :=  by sorry
