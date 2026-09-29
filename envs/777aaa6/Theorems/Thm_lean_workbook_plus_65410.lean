-- Prove2me | Theorems.Thm_lean_workbook_plus_65410
-- name    : lean_workbook_plus_65410
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/72d04702-42d4-49b8-b034-201f61467ba7
-- statement:
--   $\sum \frac{x^{2}y(y-z)}{x+y}\ge 0 \Leftrightarrow \sum \frac{x^{2}y^{2}}{x+y}\geq xyz\sum \frac{x}{x+y}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65410 : ∀ x y z : ℝ, ∑ x in {x, y, z}, (x^2 * y * (y - z)) / (x + y) ≥ 0 ↔ ∑ x in {x, y, z}, (x^2 * y^2) / (x + y) ≥ x * y * z * ∑ x in {x, y, z}, x / (x + y)   :=  by sorry
