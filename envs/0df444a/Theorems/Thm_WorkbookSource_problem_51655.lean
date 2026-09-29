-- Prove2me | Theorems.Thm_WorkbookSource_problem_51655
-- name    : WorkbookSource.problem_51655
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:02.632379+00:00
-- url     : https://prove2.me/theorems/937612cb-75e1-47b6-b020-00e98d1f0419
-- title:
--   Factoring 2310 into five primes
-- statement:
--   Prove that $2310=2\cdot3\cdot5\cdot7\cdot11$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51655` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51655; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_51655 (h₁ : 2 ∣ 2310) (h₂ : 3 ∣ 2310) (h₃ : 5 ∣ 2310) (h₄ : 7 ∣ 2310) (h₅ : 11 ∣ 2310) : 2310 = 2*3*5*7*11  :=  by sorry
