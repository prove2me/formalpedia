-- Prove2me | Theorems.Thm_lean_workbook_plus_31403
-- name    : lean_workbook_plus_31403
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ecde47a8-b43f-4c23-98fd-46b797d7e2f5
-- statement:
--   Using inclusion-exclusion, the number of tuples $(x_1,\ldots,x_6)$ such that $\sum_{i=1}^6x_i=27$ and $0\le x_i\le 9$ is $\binom{32}{5}-\binom{6}{1}\binom{22}{5}+\binom{6}{2}\binom{12}{5}=201376-158004+11880=55252$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31403 (Nat.choose 32 5) - (Nat.choose 6 1 * Nat.choose 22 5) + (Nat.choose 6 2 * Nat.choose 12 5) = 55252   :=  by sorry
