-- Prove2me | Theorems.Thm_WorkbookSource_problem_30147
-- name    : WorkbookSource.problem_30147
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:36:53.851307+00:00
-- url     : https://prove2.me/theorems/177f2b8f-6003-470a-b6c8-ffa3ea4035e7
-- title:
--   A congruence that gives divisibility by five
-- statement:
--   Prove that if $p\equiv 2\pmod 5$, then $5\vert 2p+1$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30147` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30147; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_30147 (p : ℕ) (hp : p ≡ 2 [ZMOD 5]) : 5 ∣ 2 * p + 1  :=  by sorry
