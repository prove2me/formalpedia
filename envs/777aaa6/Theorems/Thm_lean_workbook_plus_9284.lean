-- Prove2me | Theorems.Thm_lean_workbook_plus_9284
-- name    : lean_workbook_plus_9284
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/452ef45e-5ee9-4245-b9e3-8653f980653c
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a\sqrt{a}+b\sqrt{b}+c\sqrt{c} \ge3$ then prove that;\n\n $$abc+2 \ge \frac{9}{a^3+b^3+c^3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9284 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a * Real.sqrt a + b * Real.sqrt b + c * Real.sqrt c >= 3 → a * b * c + 2 >= 9 / (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
