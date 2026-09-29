-- Prove2me | Theorems.Thm_lean_workbook_plus_59333
-- name    : lean_workbook_plus_59333
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8ddad562-5bd7-4d65-b1d9-b5b95945a776
-- statement:
--   Find $\alpha$, $\beta$, $\gamma$ such that: $\frac {a^2}{bc} + \frac {b^2}{ca} + \frac {c^2}{ab} \le \alpha + \beta + \gamma$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59333 (a b c α β γ : ℝ) : a > 0 ∧ b > 0 ∧ c > 0 → α = a^2 / b / c ∧ β = b^2 / c / a ∧ γ = c^2 / a / b → a^2 / b / c + b^2 / c / a + c^2 / a / b ≤ α + β + γ   :=  by sorry
