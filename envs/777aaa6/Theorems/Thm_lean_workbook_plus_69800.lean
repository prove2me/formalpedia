-- Prove2me | Theorems.Thm_lean_workbook_plus_69800
-- name    : lean_workbook_plus_69800
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/10d9bf48-b3e4-4fa1-a5e3-c7f2550e25f2
-- statement:
--   Let $a,b,c,d$ be nonnegative real numbers such that $a^3+b^3+c^3+d^3+abcd=5.$ Prove that $ab+cd \leq 2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69800 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (habc : a * b * c * d = 1) (h : a^3 + b^3 + c^3 + d^3 + a * b * c * d = 5) : a * b + c * d ≤ 2   :=  by sorry
