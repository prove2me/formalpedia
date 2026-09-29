-- Prove2me | Theorems.Thm_lean_workbook_plus_46215
-- name    : lean_workbook_plus_46215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/f0f02e73-a14e-47a3-b196-ed68a9d432a9
-- statement:
--   xy(x + y) = 30 \Rightarrow x + y = \frac{30}{xy} . Substitute into the second equation: xy + \frac{30}{xy} = 11 . Find xy: $x^2y^2 + 30 = 11xy \Rightarrow x^2y^2 - 11xy + 30 = 0 \Rightarrow (xy - 6)(xy - 5) = 0$ . So, xy = 6 or xy = 5 .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46215  (x y : ℝ)
  (h₀ : x * y * (x + y) = 30)
  (h₁ : x * y + (30 / (x * y)) = 11) :
  x + y = (30 / (x * y))   :=  by sorry
