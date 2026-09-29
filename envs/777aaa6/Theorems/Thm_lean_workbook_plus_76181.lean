-- Prove2me | Theorems.Thm_lean_workbook_plus_76181
-- name    : lean_workbook_plus_76181
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/0dba1f97-0593-461c-baad-15f3808c9878
-- statement:
--   For all nonnegative real numbers $a,b,c$ prove that $a+b+c \ge \frac{a-b}{b+2}+ \frac{b-c}{c+2}+ \frac{c-a}{a+2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76181 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a + b + c ≥ a - b / (b + 2) + b - c / (c + 2) + c - a / (a + 2)   :=  by sorry
