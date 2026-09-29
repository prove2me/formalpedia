-- Prove2me | Theorems.Thm_lean_workbook_plus_30241
-- name    : lean_workbook_plus_30241
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b5d7a28a-edeb-4f83-ad3f-fcbec2b6c0c5
-- statement:
--   Write $P(x)=x(x-1)(x-2)Q(x)+ax^2+bx+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30241 (a b c : ℝ) (Q : ℝ → ℝ) (P : ℝ → ℝ) (h₁ : P = fun x => x * (x - 1) * (x - 2) * Q x + a * x ^ 2 + b * x + c) : ∃ a b c : ℝ, ∀ x : ℝ, P x = x * (x - 1) * (x - 2) * Q x + a * x ^ 2 + b * x + c   :=  by sorry
