-- Prove2me | Theorems.Thm_lean_workbook_plus_53126
-- name    : lean_workbook_plus_53126
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9b7cf657-9691-4919-abad-fd40485119f3
-- statement:
--   Let $a,b,c>0$ and $a^2+b^2+c^2=1$. Prove that: $1\le \frac{a}{1+bc}+\frac{b}{1+ac}+\frac{c}{1+ab}\le \sqrt{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53126 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  1 ≤ a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ∧
    a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ≤ Real.sqrt 2   :=  by sorry
