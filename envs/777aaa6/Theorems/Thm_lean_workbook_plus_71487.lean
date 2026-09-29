-- Prove2me | Theorems.Thm_lean_workbook_plus_71487
-- name    : lean_workbook_plus_71487
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/bc27c948-aac6-4740-993c-1c7877daceb6
-- statement:
--   Is $f(x) = \sin{\frac{1}{x}}$ for $x\ne 0$ and $0$ for $x=0$ a function?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71487 : ∃ f : ℝ → ℝ, ∀ x, f x = if x = 0 then 0 else sin (1/x)   :=  by sorry
