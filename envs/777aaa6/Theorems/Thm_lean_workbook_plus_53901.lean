-- Prove2me | Theorems.Thm_lean_workbook_plus_53901
-- name    : lean_workbook_plus_53901
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/2cddeb4a-8e69-494f-a313-7cb6da8fd6c5
-- statement:
--   Finally, plugging in $x = 5$ gives $f(5) = \frac{3}{4}(5-1)^2 = \boxed{12}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53901  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (3 / 4) * (x - 1)^2)
  (h₁ : x = 5) :
  f x = 12   :=  by sorry
