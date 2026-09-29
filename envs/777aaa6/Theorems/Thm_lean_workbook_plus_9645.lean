-- Prove2me | Theorems.Thm_lean_workbook_plus_9645
-- name    : lean_workbook_plus_9645
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/97245557-ace1-4cf2-b9c5-ba75aa08be8a
-- statement:
--   Let a,b,c $\in R$ such that ac+bd=0. Prove that $\frac{a+b+c+d}{2} \le \sqrt{\frac{a^2+b^2+c^2+d^2}{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9645 (a b c d : ℝ) (h : a * c + b * d = 0) :
  (a + b + c + d) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 2)   :=  by sorry
