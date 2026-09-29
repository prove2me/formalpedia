-- Prove2me | Theorems.Thm_lean_workbook_plus_80259
-- name    : lean_workbook_plus_80259
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/33eaec38-4ce4-4272-b8cd-9a2e8b363b75
-- statement:
--   Prove that if $a, b, c>0$, then \n $\frac{1}{2}\left ( a^{2}+b^{2}+c^{2}+\frac{9abc}{a+b+c}-2ab-2bc-2ca \right )+\frac{7}{4}\left ( \left ( a-b \right )^{2}+\left ( b-c \right ) ^{2}+\left ( c-a \right )^{2}\right )\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80259 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + (9 * a * b * c) / (a + b + c) - 2 * a * b - 2 * b * c - 2 * c * a) + (7 / 4) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥ 0   :=  by sorry
