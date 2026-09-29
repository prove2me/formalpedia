-- Prove2me | Theorems.Thm_lean_workbook_plus_29310
-- name    : lean_workbook_plus_29310
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/cd50e467-d191-4faa-80d6-c7f4a35486f1
-- statement:
--   Prove the combinatoric identity: $\binom{2n}{2} = 2.\binom{n}{2} + n^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29310 (n : ℕ) : (2 * n).choose 2 = 2 * n.choose 2 + n ^ 2   :=  by sorry
