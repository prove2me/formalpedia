-- Prove2me | Theorems.Thm_lean_workbook_plus_14439
-- name    : lean_workbook_plus_14439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/afabb461-a784-4dd8-9fc6-76ad82be2e4d
-- statement:
--   Let $a$ , $b$ and $c$ $>0$ such that: $a^2+b^2+c^2 \leq abc$ , show that: $\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{a+c} \leq \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14439 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 ≤ a * b * c) : 1 / (a + b) + 1 / (b + c) + 1 / (a + c) ≤ 1 / 2   :=  by sorry
