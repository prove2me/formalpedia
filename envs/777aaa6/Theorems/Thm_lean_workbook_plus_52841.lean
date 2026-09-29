-- Prove2me | Theorems.Thm_lean_workbook_plus_52841
-- name    : lean_workbook_plus_52841
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/c65eb16a-61ac-4e32-8737-068b7cb72965
-- statement:
--   For k=1,we have: $ \frac{(a+b)^2}{c^2+ab}+ \frac{(b+c)^2}{a^2+bc}+ \frac{(c+a)^2}{b^2+ca} \ge 6$ (Darij grinberg)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52841 :
  ∀ a b c : ℝ,
    (a + b) ^ 2 / (c ^ 2 + a * b) + (b + c) ^ 2 / (a ^ 2 + b * c) + (c + a) ^ 2 / (b ^ 2 + c * a) ≥
      6   :=  by sorry
