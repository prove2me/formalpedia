-- Prove2me | Theorems.Thm_lean_workbook_plus_41773
-- name    : lean_workbook_plus_41773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d52eeb70-4fa7-4ad2-8ae3-5c342ad188ab
-- statement:
--   Thus $3\left(13-d^{2}\right)\geq\left(7-d\right)^{2}\Leftrightarrow 2d^{2}-7d+5\leq0\Leftrightarrow\left(d-1\right)\left(2d-5\right)\leq0\Rightarrow d\leq\frac{5}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41773  (d : ℝ)
  (h₀ : 3 * (13 - d^2) ≥ (7 - d)^2) :
  d ≤ 5 / 2   :=  by sorry
