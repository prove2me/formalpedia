-- Prove2me | Theorems.Thm_lean_workbook_plus_64786
-- name    : lean_workbook_plus_64786
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/db516c4f-0b6e-4869-8525-f5523595422b
-- statement:
--   Let $\{F_n\}$ be a sequence defined as: $F_0=F_1=F_2=1$ , and $F_n=F_{n-3}+F_{n-2}+F_{n-1}$ for all integer $n\ge 3$ . Evaulate $\sum_{i=0}^\infty \frac{F_i}{2^i}=\frac{1}{1}+\frac{1}{2}+\frac{1}{4}+\frac{3}{8}+\frac{5}{16}+\frac{9}{32}+\frac{17}{64}......$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64786 : ∑' i : ℕ, (fib i) / 2^i = 6   :=  by sorry
