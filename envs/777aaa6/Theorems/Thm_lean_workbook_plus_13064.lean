-- Prove2me | Theorems.Thm_lean_workbook_plus_13064
-- name    : lean_workbook_plus_13064
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/554f2876-6e90-48a5-aedb-30ce13a58c04
-- statement:
--   $a_n^2=\frac{1\cdot3}{2^2}\cdot\frac{3\cdot5}{4^2}\cdot . . . \cdot \frac{(2n-1)\cdot(2n+1)}{(2n)^2}\cdot\frac{1}{2n+1}<1\cdot 1 . . .\cdot 1\cdot\frac{1}{2n+1}=\frac{1}{2n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13064 : ∀ n, (∏ i in Finset.range (n+1), (2 * i + 1) / (2 * i) ^ 2) * (1 / (2 * n + 1)) < (1 / (2 * n + 1))   :=  by sorry
