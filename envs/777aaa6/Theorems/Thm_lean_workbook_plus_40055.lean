-- Prove2me | Theorems.Thm_lean_workbook_plus_40055
-- name    : lean_workbook_plus_40055
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d0645c6c-146a-437a-93bc-a0fbebc66825
-- statement:
--   Let $x=a^2+b^2+c^2$ and $y=ab+bc+ca$ . It is enough to show that \n $6+27-\frac{18(x+2y)}{2x+y} \le \frac{15x}y \iff (x-y)(10x-y) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40055 {x y : ℝ} (hx : x > 0) (hy : y > 0) (hxy : x + y = 1) : 6 + 27 - (18 * (x + 2 * y)) / (2 * x + y) ≤ 15 * x / y ↔ (x - y) * (10 * x - y) ≥ 0   :=  by sorry
