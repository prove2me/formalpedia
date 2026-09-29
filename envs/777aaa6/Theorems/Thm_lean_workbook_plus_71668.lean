-- Prove2me | Theorems.Thm_lean_workbook_plus_71668
-- name    : lean_workbook_plus_71668
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c08bda42-40ff-40a2-aaf7-f1a8ca216b07
-- statement:
--   Given the functional equation $f(f(x))=f(x)+8x$, show that $f$ is injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71668 (f : ℝ → ℝ) (hf : ∀ x, f (f x) = f x + 8 * x) : Function.Injective f   :=  by sorry
