-- Prove2me | Theorems.Thm_WorkbookSource_problem_18636
-- name    : WorkbookSource.problem_18636
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:37:09.502296+00:00
-- url     : https://prove2.me/theorems/9cb38e5a-dc61-4820-965b-23a3364b0d32
-- title:
--   A power of two modulo thirteen
-- statement:
--   Find the remainder when $2^{2009}$ is divided by $13$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18636` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18636; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_18636 : 2 ^ 2009 ≡ 6 [ZMOD 13]  :=  by sorry
