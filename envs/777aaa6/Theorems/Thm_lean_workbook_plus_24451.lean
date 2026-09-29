-- Prove2me | Theorems.Thm_lean_workbook_plus_24451
-- name    : lean_workbook_plus_24451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/441b67ea-e736-41df-9656-ad1c192e8e4d
-- statement:
--   Is a linear function: $f(x)=ax$ . $2008a=3012\implies a=\frac{3012}{2008}$ . $f(2009)=\frac{3012\cdot 2009}{2008}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24451  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x)
  (h₁ : 2008 * a = 3012) :
  f 2009 = 3012 * 2009 / 2008   :=  by sorry
