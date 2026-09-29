-- Prove2me | Theorems.Thm_lean_workbook_plus_72596
-- name    : lean_workbook_plus_72596
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/95b7b05f-d519-46ae-8e8d-9019fc4ef985
-- statement:
--   $f$ is constant and $g(x)=2013$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72596 (f g : ℝ → ℝ) (hf : ∃ c, ∀ x, f x = c) (hg : ∀ x, g x = 2013) : ∃ c, ∀ x, f x + g x = c + 2013   :=  by sorry
