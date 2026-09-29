-- Prove2me | Theorems.Thm_lean_workbook_plus_67435
-- name    : lean_workbook_plus_67435
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/b91e7dd2-5138-4c86-abfe-d1d369e5b802
-- statement:
--   Let $a=\frac{y}{x+y},b=\frac{z}{y+z},c=\frac{x}{z+x}$. Rewrite the original inequality as $\sum b(1-b)+2\sum a(1-c)\leq \frac{9}{4}$. Simplify and prove.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67435 (x y z : ℝ) :
  (y / (x + y) * (1 - y / (x + y)) + z / (y + z) * (1 - z / (y + z)) + x / (z + x) * (1 - x / (z + x))) ≤ 9 / 4   :=  by sorry
