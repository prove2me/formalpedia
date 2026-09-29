-- Prove2me | Theorems.Thm_lean_workbook_plus_10545
-- name    : lean_workbook_plus_10545
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/21883850-8c08-4160-a305-c08181980c43
-- statement:
--   $\forall x\neq 0, \frac{f(x)}{x}=\frac{f(1)}{1} \implies f(x)=f(1)x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10545 (f : ℝ → ℝ) (hf: ∀ x, x ≠ 0 → f x / x = f 1 / 1) : ∀ x, x ≠ 0 → f x = f 1 * x   :=  by sorry
