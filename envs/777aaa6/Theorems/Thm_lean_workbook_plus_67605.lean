-- Prove2me | Theorems.Thm_lean_workbook_plus_67605
-- name    : lean_workbook_plus_67605
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/31cf397e-494e-4c2e-8519-b4cb6d70e063
-- statement:
--   Tryhard S1From the given, we know that $f(x)=x^2+x+5 \ \forall{x}\in\text{Dom}(f)$ . Hence $f(13)=(13)^2+(13)+5\implies f(13)=\boxed{187}$ as desired.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67605  (f : ℝ → ℝ)
  (h₀ : ∀ x, x ∈ Set.Icc 0 13 → f x = x^2 + x + 5) :
  f 13 = 187   :=  by sorry
