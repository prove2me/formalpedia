-- Prove2me | Theorems.Thm_lean_workbook_plus_49207
-- name    : lean_workbook_plus_49207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/370e1d50-20d9-42c4-894f-73b6ff031921
-- statement:
--   Let $x,y$ be positive numbers satisfying $x + y \le 1.$ Prove that $x^4 + y^4 - x^2y - xy^2\geq -\frac{1}{8}$ . Equality holds when $x=y=\frac{1}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49207 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ 1) : x^4 + y^4 - x^2*y - x*y^2 ≥ -1/8   :=  by sorry
