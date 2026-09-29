-- Prove2me | Theorems.Thm_lean_workbook_plus_55919
-- name    : lean_workbook_plus_55919
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ea216900-1e2d-4f69-ad10-4290d7fa2065
-- statement:
--   Set up a system. Let $p$ denote the weight of pizza and $o$ denote the weight of orange slices. Thus we have, $\frac{1}{3} \cdot p + \frac{7}{2} \cdot o = \frac{3}{4} \cdot p + \frac{1}{2} \cdot o$ This simplifies to $\frac{36}{5} \cdot o = p$ . Then substituting $o = \frac{1}{4}$ we find $p = \frac{9}{5}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55919 (p o : ℝ) : (1 / 3 * p + 7 / 2 * o = 3 / 4 * p + 1 / 2 * o) → (o = 1 / 4 → p = 9 / 5)   :=  by sorry
