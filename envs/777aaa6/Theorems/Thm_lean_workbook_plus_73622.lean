-- Prove2me | Theorems.Thm_lean_workbook_plus_73622
-- name    : lean_workbook_plus_73622
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/6ecb4c37-ee75-4bbe-8deb-f5cec8693e4d
-- statement:
--   The number of solutions to the equation $x_1 + x_2 + x_3 + x_4 + x_5 = 12$ is $\binom{12+4}{4}=\boxed {\binom{16}{4}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73622 (Nat.choose 16 4) = (Nat.choose (12+4) 4)   :=  by sorry
