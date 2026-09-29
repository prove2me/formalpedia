-- Prove2me | Theorems.Thm_lean_workbook_plus_70240
-- name    : lean_workbook_plus_70240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7ce374ec-f23f-45e4-8554-90f88b1809b9
-- statement:
--   It is equivalent to $ab\le b^2+ac$ \n\n $\leftrightarrow (b-\frac{a}{2})^2+a(c-\frac{a}{4}) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70240 (a b c : ℝ) :
  a * b ≤ b^2 + a * c ↔ (b - a / 2)^2 + a * (c - a / 4) ≥ 0   :=  by sorry
