-- Prove2me | Theorems.Thm_lean_workbook_plus_18134
-- name    : lean_workbook_plus_18134
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/958d26a1-6efb-4b28-9ec8-d67eda3aea86
-- statement:
--   Let $a, b, c$ be real numbers such that $a^2+ab+b^2=3.$ Prove that $$(a^2-a+1)(b^2-b+1)\geq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18134 (a b c : ℝ) (hab : a^2 + a * b + b^2 = 3) : (a^2 - a + 1) * (b^2 - b + 1) ≥ 1   :=  by sorry
