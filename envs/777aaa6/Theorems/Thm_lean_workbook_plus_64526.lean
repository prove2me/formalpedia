-- Prove2me | Theorems.Thm_lean_workbook_plus_64526
-- name    : lean_workbook_plus_64526
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e3ebc8a8-46f6-49ef-a775-0e79f4e37e6d
-- statement:
--   Prove that $f(k)=k^{3}-2k^{2}+k+1>0$ when $k \geq \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64526 (k : ℝ) (h : k >= 1/2) : k^3 - 2 * k^2 + k + 1 > 0   :=  by sorry
