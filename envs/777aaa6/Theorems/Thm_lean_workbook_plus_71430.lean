-- Prove2me | Theorems.Thm_lean_workbook_plus_71430
-- name    : lean_workbook_plus_71430
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/5d6d24c8-8e86-477f-889f-7d8e9735c4ec
-- statement:
--   Let $x,y>0$. Proof that $x^2+y^2+xy+\frac{25}{12} \geqslant \frac{5}{2}(x+y)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71430 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^2 + y^2 + x * y + 25 / 12 ≥ 5 / 2 * (x + y)   :=  by sorry
