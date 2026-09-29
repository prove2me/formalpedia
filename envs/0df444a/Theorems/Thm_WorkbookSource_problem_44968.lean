-- Prove2me | Theorems.Thm_WorkbookSource_problem_44968
-- name    : WorkbookSource.problem_44968
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:14.888914+00:00
-- url     : https://prove2.me/theorems/217591fd-381f-4350-a208-25a10f121d92
-- title:
--   Euler’s totient at83
-- statement:
--   Find the value of Euler's totient function, $\phi(n)$, for $n = 83$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44968` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Notation repair: Expanded scoped notation into Nat.totient or Real.sqrt; the elaborated mathematical expression and binders are unchanged.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44968; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_44968 (n : ℕ) (hn : n = 83) : Nat.totient n = 82  :=  by sorry
