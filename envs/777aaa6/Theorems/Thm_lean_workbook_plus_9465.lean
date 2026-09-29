-- Prove2me | Theorems.Thm_lean_workbook_plus_9465
-- name    : lean_workbook_plus_9465
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2919d552-4766-4c5f-b650-f0bbec90ff33
-- statement:
--   Prove that \(\binom{n+2}{4}=\binom{n}{2}+2\binom{n}{3}+\binom{n}{4}\) using Pascal's triangle.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9465 (n : ℕ) : choose (n + 2) 4 = choose n 2 + 2 * choose n 3 + choose n 4   :=  by sorry
