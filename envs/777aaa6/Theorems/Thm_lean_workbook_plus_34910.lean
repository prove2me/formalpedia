-- Prove2me | Theorems.Thm_lean_workbook_plus_34910
-- name    : lean_workbook_plus_34910
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/308a97e8-670b-46a6-b5cc-5900d4f4f7e7
-- statement:
--   Prove that for a real number $t$, we have $f(t)=0$ or $f(t)=t^2$. Also, prove that if $f(\alpha)=0$ for a $\alpha\neq 0$, then $f(x)\equiv 0$. If $f(x)\neq 0$ for all $x\neq 0$, then prove that $f(x)\equiv x^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34910 (f : ℝ → ℝ) (hf : ∀ t, f t = 0 ∨ ∀ t, f t = t ^ 2) : (∀ α ≠ 0, f α = 0 → ∀ x, f x = 0) ∨ (∀ x ≠ 0, f x ≠ 0 → ∀ x, f x = x ^ 2)   :=  by sorry
