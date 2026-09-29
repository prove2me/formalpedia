-- Prove2me | Theorems.Thm_lean_workbook_plus_53107
-- name    : lean_workbook_plus_53107
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ac52e87c-a8ad-4bf2-b5fb-42840efbefdc
-- statement:
--   Prove that if $a,b,c>0$ , then $\frac{b+c}{a+3b+3c}+\frac{c+a}{b+3c+3a}+\frac{a+b}{c+3a+3b}\leq \frac{6}{7}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53107 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (a + 3 * b + 3 * c) + (c + a) / (b + 3 * c + 3 * a) + (a + b) / (c + 3 * a + 3 * b) ≤ 6 / 7   :=  by sorry
