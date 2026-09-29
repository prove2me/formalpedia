-- Prove2me | Theorems.Thm_lean_workbook_plus_71703
-- name    : lean_workbook_plus_71703
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/203157ff-2349-4f4b-a8c0-4b38d6be9606
-- statement:
--   $\sqrt{\frac{y^{2}+z^{2}}{x^{2}}}\leq \frac{{1+\frac{y^{2}+z^{2}}{x^{2}}}}{2}=\frac{x^{2}+y^{2}+z^{2}}{2x^{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71703 (x y z : ℝ) (hx : x ≠ 0) : Real.sqrt ((y ^ 2 + z ^ 2) / x ^ 2) ≤ (1 + (y ^ 2 + z ^ 2) / x ^ 2) / 2   :=  by sorry
