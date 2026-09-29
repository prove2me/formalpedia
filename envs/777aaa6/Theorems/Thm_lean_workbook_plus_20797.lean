-- Prove2me | Theorems.Thm_lean_workbook_plus_20797
-- name    : lean_workbook_plus_20797
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/34c9d81c-3007-4020-8209-b1f00e8727b8
-- statement:
--   Let a,b,c,d positive reals, so that $a+b+c+d=1$ . Proof that $ab+ac+ad+bc+bd+cd\leq \frac{3}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20797 (a b c d : ℝ) (h : a + b + c + d = 1) :
  a * b + a * c + a * d + b * c + b * d + c * d ≤ 3 / 8   :=  by sorry
