-- Prove2me | Theorems.Thm_lean_workbook_plus_32025
-- name    : lean_workbook_plus_32025
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c0188cb6-fae7-4fa9-bf10-2114b9a1f4cc
-- statement:
--   By Rearrangement Inequality we have $a^4+b^4+c^4 \geqslant |b^3c| + |c^3a| + |a^3b| \geqslant -b^3c -c^3a -a^3b$ , so $ ab^3+bc^3+ca^3 = \sum_{cyc} (-b-c)b^3 \leqslant 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32025  (a b c : ℝ)
  (h₀ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c)
  (h₁ : a + b + c = 0) :
  a * b^3 + b * c^3 + c * a^3 ≤ 0   :=  by sorry
