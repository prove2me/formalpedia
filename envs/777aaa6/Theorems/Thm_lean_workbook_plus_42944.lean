-- Prove2me | Theorems.Thm_lean_workbook_plus_42944
-- name    : lean_workbook_plus_42944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c04d5a54-e7fd-4203-83d8-11ae67b69614
-- statement:
--   I think it should be \n\n $16(abc+bcd+cda+dab) \leq (a+b+c+d)^{3}$ \n\n which is true for $a,b,c,d\ge 0$ and very easy
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42944 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : 16 * (a * b * c + b * c * d + c * d * a + d * a * b) ≤ (a + b + c + d) ^ 3   :=  by sorry
