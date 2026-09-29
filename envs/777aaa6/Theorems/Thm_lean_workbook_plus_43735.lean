-- Prove2me | Theorems.Thm_lean_workbook_plus_43735
-- name    : lean_workbook_plus_43735
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c629ed94-748f-4fbc-b000-0b9b8304ce63
-- statement:
--   Given $P_n = \frac {3n^2 - n}{2}, T_{n-1} = \frac {(n-1)(n)}{2}$, prove that $P_n=3T_{n-1}+n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43735 (n : ℕ) : 3 * ((n - 1) * n) / 2 + n = (3 * n ^ 2 - n) / 2   :=  by sorry
