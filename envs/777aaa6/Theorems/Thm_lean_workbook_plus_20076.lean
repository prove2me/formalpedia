-- Prove2me | Theorems.Thm_lean_workbook_plus_20076
-- name    : lean_workbook_plus_20076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6fdec9a0-243e-452c-81dc-3141dd65c438
-- statement:
--   Let $a=b+x$ and $d=c+y$ . Ineq becomes\n\n$6(x^2+y^2)+(x+y)^2+4(x+y)(b+c)+4(b+c)^2-12bc \ge 0$ ,\n\n$3(x-y)^2+3(b-c)^2+(2x+2y+b+c)^2 \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20076 {a b c d x y : ℝ} (hab : a = b + x) (hcd : d = c + y) :
  6 * (x ^ 2 + y ^ 2) + (x + y) ^ 2 + 4 * (x + y) * (b + c) + 4 * (b + c) ^ 2 - 12 * b * c ≥ 0 ∧
  3 * (x - y) ^ 2 + 3 * (b - c) ^ 2 + (2 * x + 2 * y + b + c) ^ 2 ≥ 0   :=  by sorry
