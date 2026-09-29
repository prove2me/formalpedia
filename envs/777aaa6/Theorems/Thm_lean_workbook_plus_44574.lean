-- Prove2me | Theorems.Thm_lean_workbook_plus_44574
-- name    : lean_workbook_plus_44574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cd18b21e-a6d5-46da-82d6-da42e1bcdec7
-- statement:
--   Let $ a,b,c>0$ and $a^4+b^4+c\leq\frac {3}{2}$ . Prove that $ abc + \frac {1}{abc}\geq\frac{5}{2}$ Equality holds when $a=b=\frac{1}{\sqrt 2},c=1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44574 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a ^ 4 + b ^ 4 + c ≤ 3 / 2) : a * b * c + 1 / (a * b * c) ≥ 5 / 2   :=  by sorry
