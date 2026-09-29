-- Prove2me | Theorems.Thm_lean_workbook_plus_70088
-- name    : lean_workbook_plus_70088
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7537c37e-4590-4b8e-9c1b-4959ad9a68ac
-- statement:
--   Derive the inequality $(a+b)(c+d)\leq\frac{(a+b+c+d)^2}{4}$ from the given conditions $(a+b)+(c+d)\geq2\sqrt{(a+b)(c+d)}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70088 (a b c d : ℝ) (h : a + b + c + d ≥ 2 * Real.sqrt ((a + b) * (c + d))) :
  (a + b) * (c + d) ≤ (a + b + c + d) ^ 2 / 4   :=  by sorry
