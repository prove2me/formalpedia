-- Prove2me | Theorems.Thm_lean_workbook_plus_37471
-- name    : lean_workbook_plus_37471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9be2989c-5358-4ea8-8ed6-fe34995aeee6
-- statement:
--   $P(2,2): f(2)^2=2f(2)+8 \\implies f(2)=4$ or $f(2)=-2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37471 (f : ℤ → ℤ) (h₁ : f 2 ^ 2 = 2 * f 2 + 8) : f 2 = 4 ∨ f 2 = -2   :=  by sorry
