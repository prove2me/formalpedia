-- Prove2me | Theorems.Thm_lean_workbook_plus_2110
-- name    : lean_workbook_plus_2110
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a3c2b8ee-aa4f-4867-914f-89521bbe602b
-- statement:
--   Given $\alpha\beta\gamma = \alpha + \beta + \gamma + 2$, prove $\alpha +\beta +\gamma \geq 6\Rightarrow \alpha \beta \gamma \geq 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2110 (α β γ : ℝ) (h : α + β + γ ≥ 6) (habc : α * β * γ = α + β + γ + 2) : α * β * γ ≥ 8   :=  by sorry
