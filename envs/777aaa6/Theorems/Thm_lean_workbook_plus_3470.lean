-- Prove2me | Theorems.Thm_lean_workbook_plus_3470
-- name    : lean_workbook_plus_3470
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5872ab3c-6083-445e-8913-ac9ce5f1487a
-- statement:
--   Replace $x+3$ with $z$ . Now we have $f(z)=3(z-3)^2+7(z-3)+4=3z^2-18z+27+7z-21+4=3z^2-11z+10$ . Because this holds for all reals, we can simply substitute $x$ for $z$ again to get $f(x)=y=3x^2-11x+10$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3470  (x y : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ z, f z = 3 * (z - 3)^2 + 7 * (z - 3) + 4)
  (h₁ : y = f x) :
  y = 3 * x^2 - 11 * x + 10   :=  by sorry
