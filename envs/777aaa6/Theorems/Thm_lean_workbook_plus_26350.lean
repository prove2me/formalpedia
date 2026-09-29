-- Prove2me | Theorems.Thm_lean_workbook_plus_26350
-- name    : lean_workbook_plus_26350
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/5b270a60-54b7-4117-9b68-abaacd95c490
-- statement:
--   Finding $\binom{50}{6}-\binom{5}{1}\binom{40}{6}+\binom{5}{2}\binom{30}{6}-\binom{5}{3}\binom{20}{6}+\binom{5}{4}\binom{10}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26350 : (choose 50 6) - (choose 5 1 * choose 40 6) + (choose 5 2 * choose 30 6) - (choose 5 3 * choose 20 6) + (choose 5 4 * choose 10 6) = 2250000   :=  by sorry
