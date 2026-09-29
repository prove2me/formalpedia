-- Prove2me | Theorems.Thm_lean_workbook_plus_35818
-- name    : lean_workbook_plus_35818
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/d168f177-46ce-4990-b016-5a1c9d5a9325
-- statement:
--   Show that\n\n $$\frac{3}{1*2*4}+\frac{4}{2*3*5}+\frac{5}{3*4*6} + \cdots + \frac{n+2}{n(n+1)(n+3)}=\frac{1}{6}\left[\frac{29}{6}-\frac{4}{n+1}-\frac{1}{n+2}-\frac{1}{n+3}\right]$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35818 (n : ℕ) : ∑ k in Finset.Icc 1 n, (3 + k) / (k * (k + 1) * (k + 3)) = 1 / 6 * (29 / 6 - 4 / (n + 1) - 1 / (n + 2) - 1 / (n + 3))   :=  by sorry
