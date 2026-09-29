-- Prove2me | Theorems.Thm_lean_workbook_plus_53370
-- name    : lean_workbook_plus_53370
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/37c2144d-f4b6-485b-ba31-1f255b085871
-- statement:
--   Find the value of $f(x+8) - f(x+7) - f(x+6) + f(x+5) - f(x+4) + f(x+3) + f(x+2) -f(x+1)$, where $f(x) = 7x^3 + 23x + 18$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53370 (f : ℤ → ℤ) (x : ℤ) (f_def : ∀ x, f x = 7 * x ^ 3 + 23 * x + 18) : f (x + 8) - f (x + 7) - f (x + 6) + f (x + 5) - f (x + 4) + f (x + 3) + f (x + 2) - f (x + 1) = 336   :=  by sorry
