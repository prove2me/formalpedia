-- Prove2me | Theorems.Thm_lean_workbook_plus_4325
-- name    : lean_workbook_plus_4325
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/de446804-d66c-4cff-95e6-cf0ae4f5412e
-- statement:
--   Let $x, y \in \mathbb{R}$ and $| 2x-y |\le 3$ and $| x-3y | \le 1$ . Find maximum value of $P=x^2+xy+y^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4325 (x y : ℝ) (h1 : abs (2*x - y) ≤ 3) (h2 : abs (x - 3*y) ≤ 1) : x^2 + x*y + y^2 ≤ 7   :=  by sorry
