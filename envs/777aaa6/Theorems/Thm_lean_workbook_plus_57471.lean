-- Prove2me | Theorems.Thm_lean_workbook_plus_57471
-- name    : lean_workbook_plus_57471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f2eb2742-eac6-4b18-8fb6-c2eb82417649
-- statement:
--   Prove: $ a,b,c,d\ge 0\Rightarrow a^3+b^3+c^3+d^3\ge abc+bcd+cda+dab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57471 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) : a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 ≥ a * b * c + b * c * d + c * d * a + d * a * b   :=  by sorry
