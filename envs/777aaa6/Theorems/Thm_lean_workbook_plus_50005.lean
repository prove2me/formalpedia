-- Prove2me | Theorems.Thm_lean_workbook_plus_50005
-- name    : lean_workbook_plus_50005
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/917e9cc9-33f3-4128-81ee-7841441e0ff1
-- statement:
--   Let $a,b,c,d$ are positive number and they are different with 1 such that $a^{2}+b^{2}+c^{2}+d^{2}=1$ . Prove that: $(1-a)(1-b)(1-c)(1-d)\ge abcd$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50005 (a b c d : ℝ) (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hd : d ≠ 1) (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (habc : a ≠ c) (habd : a ≠ d) (hbd : b ≠ d) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 1) : (1 - a) * (1 - b) * (1 - c) * (1 - d) ≥ a * b * c * d   :=  by sorry
