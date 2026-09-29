-- Prove2me | Theorems.Thm_lean_workbook_plus_59761
-- name    : lean_workbook_plus_59761
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d24310c2-838f-47c7-8ec2-95acd20e8f25
-- statement:
--   Given three non-negative numbers $a, b, c$ so that $1\leqq a, b, c\leqq 3$ .\n $$\sum\frac{3}{a}+ \frac{45}{a+ b+ c}\geqq\sum\frac{16}{a+ b}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59761 (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 3) (hb : 1 ≤ b ∧ b ≤ 3) (hc : 1 ≤ c ∧ c ≤ 3) : 3 / a + 45 / (a + b + c) ≥ 16 / (a + b)   :=  by sorry
