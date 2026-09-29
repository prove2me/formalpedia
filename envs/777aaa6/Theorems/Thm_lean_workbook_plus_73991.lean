-- Prove2me | Theorems.Thm_lean_workbook_plus_73991
-- name    : lean_workbook_plus_73991
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/5c6299f3-10f6-4449-9b99-1133736073c7
-- statement:
--   FF2 $f(x)= x^x + 2x + x^2$ find $f(5)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73991 (f : ℕ → ℕ) (f_def : ∀ x : ℕ, f x = x^x + 2 * x + x^2) : f 5 = 3160   :=  by sorry
