-- Prove2me | Theorems.Thm_lean_workbook_plus_17682
-- name    : lean_workbook_plus_17682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6e5bfdd6-406e-4711-9a1d-dba5d390632d
-- statement:
--   Let $a,b,c>0$ and $\frac{1}{(a-1)(b-1)(c-1)}-\frac{4}{(a+1)(b+1)(c+1)}=\frac{1}{16}$ . Prove that $$\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\geq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17682 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : (1 / (a - 1) / (b - 1) / (c - 1) - 4 / (a + 1) / (b + 1) / (c + 1) = 1 / 16) → 1 / a + 1 / b + 1 / c ≥ 1   :=  by sorry
