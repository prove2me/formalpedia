-- Prove2me | Theorems.Thm_lean_workbook_plus_52744
-- name    : lean_workbook_plus_52744
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/1452a14e-d8d2-4fe1-86a1-fad8cec9feee
-- statement:
--   Let a,b,c,d>0 such that: $a^2+b^2=c^2+d^2$ Prove that : $(a+b)(c+d)>=2 (ab+cd)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52744 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a^2 + b^2 = c^2 + d^2) : (a + b) * (c + d) ≥ 2 * (a * b + c * d)   :=  by sorry
