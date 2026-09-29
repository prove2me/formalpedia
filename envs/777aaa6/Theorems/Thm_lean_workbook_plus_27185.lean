-- Prove2me | Theorems.Thm_lean_workbook_plus_27185
-- name    : lean_workbook_plus_27185
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2c67750d-febf-47f8-9361-465292a27c99
-- statement:
--   Prove the identity combinatorially: $\binom{2n}{2}= 2\binom{n}{2} +n^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27185 : ∀ n : ℕ, choose (2 * n) 2 = 2 * choose n 2 + n ^ 2   :=  by sorry
