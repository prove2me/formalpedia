-- Prove2me | Theorems.Thm_lean_workbook_plus_60880
-- name    : lean_workbook_plus_60880
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/510efcd1-4220-45a7-96d7-b085a20a6aa2
-- statement:
--   Since these two equations are independent of each other (the variables don't coincide in the two separate equations), the Fundamental Counting Principle tells us to multiply these two answers: $\binom{7}{2}\binom{16}{1} \implies 21*16 \implies \boxed{336}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60880 (Nat.choose 7 2 * Nat.choose 16 1) = 336   :=  by sorry
