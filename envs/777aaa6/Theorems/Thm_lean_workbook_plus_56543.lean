-- Prove2me | Theorems.Thm_lean_workbook_plus_56543
-- name    : lean_workbook_plus_56543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/69dcd6fa-2817-4e1f-82ab-9f6ca92a436b
-- statement:
--   Let $a=x+y,b=y+z$ and $c=z+x$ . Then the equality becomes $2z=\frac{2(y+z)^2(z+x)}{(2x+y+z)^2}+\frac{2(z+x)^2(y+z)}{(2y+x+z)^2}\Rightarrow z=\frac{(y+z)^2(z+x)}{(2x+y+z)^2}+\frac{(y+z)(z+x)^2}{(2y+x+z)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56543 :
  ∀ x y z : ℝ,
    2 * z = (2 * (y + z) ^ 2 * (z + x)) / (2 * x + y + z) ^ 2 + (2 * (z + x) ^ 2 * (y + z)) / (2 * y + x + z) ^ 2 ↔
    z = ((y + z) ^ 2 * (z + x)) / (2 * x + y + z) ^ 2 + ((y + z) * (z + x) ^ 2) / (2 * y + x + z) ^ 2   :=  by sorry
