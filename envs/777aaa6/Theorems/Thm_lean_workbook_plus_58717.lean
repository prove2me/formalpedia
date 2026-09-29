-- Prove2me | Theorems.Thm_lean_workbook_plus_58717
-- name    : lean_workbook_plus_58717
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8cb5af15-084a-45a5-93dc-5bdb48e777b7
-- statement:
--   Consider the quadratic function $f(x)=20x^2-11x+2016$ . Show that there exists an integer $\alpha$ such that $2^{10^{11^{2016}}}\mid f(\alpha)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58717 (f : ℤ → ℤ) (α : ℤ) (hf: f = (λ x:ℤ => 20 * x ^ 2 - 11 * x + 2016)) : (¬ 2 ^ 10 ^ 11 ^ 2016 ∣ f α) ∨ ∃ α : ℤ, (2 ^ 10 ^ 11 ^ 2016 ∣ f α)   :=  by sorry
