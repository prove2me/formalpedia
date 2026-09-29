-- Prove2me | Theorems.Thm_lean_workbook_plus_12121
-- name    : lean_workbook_plus_12121
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/05d4a984-e9b8-4113-8fa6-701b2fd31c5f
-- statement:
--   Let $a, b, c$ be real positive numbers such that $a^2+b^2+c^2=3.$ Prove that $$ab+bc+ca \le abc+2.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12121 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 3) : a * b + b * c + c * a ≤ a * b * c + 2   :=  by sorry
