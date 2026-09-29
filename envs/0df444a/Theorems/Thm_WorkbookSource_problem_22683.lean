-- Prove2me | Theorems.Thm_WorkbookSource_problem_22683
-- name    : WorkbookSource.problem_22683
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:36:59.692406+00:00
-- url     : https://prove2.me/theorems/0e6fc238-e27c-4efd-9fe0-fea10a6ef4df
-- title:
--   A fourth-power identity for powers of2002
-- statement:
--   (6·2002^n)^4+(5·2002^n)^4+(3·2002^n)^4=2002^{4n+1} for all $n\in\mathbb{N}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22683` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22683; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_22683 : ∀ n : ℕ, (6 * 2002 ^ n) ^ 4 + (5 * 2002 ^ n) ^ 4 + (3 * 2002 ^ n) ^ 4 = 2002 ^ (4 * n + 1)  :=  by sorry
