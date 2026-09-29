-- Prove2me | Theorems.Thm_lean_workbook_plus_9960
-- name    : lean_workbook_plus_9960
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/48639e99-0257-4113-840b-58bb4e37adb2
-- statement:
--   Find the monic quadratic with roots $\alpha$ and $\beta$ if $\alpha\beta=-2,\alpha^2+\beta^2=4(\alpha+\beta)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9960 (α β : ℂ) (h₁ : α * β = -2) (h₂ : α^2 + β^2 = 4 * (α + β)) : ∃ a b c : ℂ, a * x^2 + b * x + c = (x - α) * (x - β)   :=  by sorry
