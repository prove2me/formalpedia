-- Prove2me | Theorems.Thm_WorkbookSource_problem_28159
-- name    : WorkbookSource.problem_28159
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:47.877701+00:00
-- url     : https://prove2.me/theorems/4eba1b59-ade2-455f-bfd4-69da1d339ebd
-- title:
--   A translated quartic inequality
-- statement:
--   There is a number:
--   a = m - 1
--   a\in R^ +
--   So we must prove:
--   $16(a + 1)^2 + 16\leq(a + 1)^4 + 32(a + 1)$
--   $16a^2 + 32a + 32\leq(a + 1)^4 + 32a + 32$
--   $16a^2\leq(a + 1)^4$
--   $4a\leq(a + 1)^2$
--   $0\leq(a - 1)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28159` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28159; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_28159  (a : ℝ)
  (h₀ : 0 < a) :
  16 * (a + 1)^2 + 16 ≤ (a + 1)^4 + 32 * (a + 1)  :=  by sorry
