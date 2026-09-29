-- Prove2me | Theorems.Thm_lean_workbook_plus_67412
-- name    : lean_workbook_plus_67412
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/86b23674-cc68-440b-9a3e-f56210c8c94c
-- statement:
--   Show that for all real numbers $x$ and $y$ with $x > -1$ and $y > -1$ and $x + y = 1$ the inequality \n\n $$\frac{x}{y + 1} +\frac{y}{x + 1} \ge \frac23$$\nholds. When does equality apply?\n\n(Walther Janous)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67412 (x y : ℝ) (hx : x > -1) (hy : y > -1) (hxy : x + y = 1) : (x / (y + 1) + y / (x + 1)) ≥ 2 / 3   :=  by sorry
