-- Prove2me | Theorems.Thm_WorkbookSource_problem_53641
-- name    : WorkbookSource.problem_53641
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:38.757989+00:00
-- url     : https://prove2.me/theorems/de1263c9-3d1d-438e-865c-53e2dfc19aff
-- title:
--   A power of five modulo nineteen
-- statement:
--   $\gcd (5,19)=1$ , so we proceed by Euler's Totient Theorem. $\phi (19)=19-1=18$ , so $400 \, \mathrm{mod} \, 18=4$ , giving us $5^4 \equiv 6^2 \equiv 36 \equiv \boxed{17} \pmod{19}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53641` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53641; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_53641 :
  (5^400) % 19 = 17  :=  by sorry
