-- Prove2me | Theorems.Thm_lean_workbook_plus_16640
-- name    : lean_workbook_plus_16640
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7a235251-356c-477e-9977-2e54581f40ef
-- statement:
--   Let $a,b,c \in \mathbb{R}$ such that $a+b+c=3$ . Prove that $$ \frac{a^3+b^3+c^3}{3} \geq 1+(a-1)(b-1)(c-1)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16640 (a b c : ℝ) (h : a + b + c = 3) :
  (a^3 + b^3 + c^3) / 3 ≥ 1 + (a - 1) * (b - 1) * (c - 1)   :=  by sorry
