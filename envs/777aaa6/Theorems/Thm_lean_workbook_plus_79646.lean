-- Prove2me | Theorems.Thm_lean_workbook_plus_79646
-- name    : lean_workbook_plus_79646
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c1305867-a9d9-4b8d-84f4-7aa11643f985
-- statement:
--   And by C-S we have: $\frac{(2c-1)^2}{6a^2-4a+1}+\frac{(2b-1)^2}{6b^2-4b+1}\geq \frac{4c^2}{6(a^2+b^2)-4(a+b)+2}$ (because $a+b=1-c$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79646 :
  ∀ a b c : ℝ,
    a + b + c = 1 ∧ a * b + b * c + c * a = c^2 →
    (2 * c - 1)^2 / (6 * a^2 - 4 * a + 1) + (2 * b - 1)^2 / (6 * b^2 - 4 * b + 1) ≥
    4 * c^2 / (6 * (a^2 + b^2) - 4 * (a + b) + 2)   :=  by sorry
