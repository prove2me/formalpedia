-- Prove2me | Theorems.Thm_lean_workbook_plus_66590
-- name    : lean_workbook_plus_66590
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b9c9a8dd-88bf-42d7-b5ad-e993cc1cdba9
-- statement:
--   Let $ a=\frac{1}{x},b=\frac{1}{y},c=\frac{1}{z}$ . Then using $ xyz=1$ , our inequality is equivalent to $ \frac{9}{2}\le \sum\frac{x}{y+z}\cdot \sum x\le 3\sum \frac{x^{2}}{y+z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66590 :
  ∀ x y z : ℝ, 1 / x * 1 / y * 1 / z = 1 → 9 / 2 ≤ (1 / x + 1 / y + 1 / z) * (x + y + z) ∧ (1 / x + 1 / y + 1 / z) * (x + y + z) ≤ 3 * (1 / x * x + 1 / y * y + 1 / z * z)   :=  by sorry
