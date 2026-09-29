-- Prove2me | Theorems.Thm_lean_workbook_plus_20001
-- name    : lean_workbook_plus_20001
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/372fa0a3-70d7-40ce-b484-a4987a5c4535
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a^3+b^3+c^3=abc+2$ . Prove that $(1) abc\leq 1;$ $(2)a+bc\leq 2 ;$ $(3)a+b+c \leq 3 . $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20001 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) : a * b * c ≤ 1 ∧ a + b * c ≤ 2 ∧ a + b + c ≤ 3   :=  by sorry
