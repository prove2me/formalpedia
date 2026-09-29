-- Prove2me | Theorems.Thm_WorkbookSource_problem_34657
-- name    : WorkbookSource.problem_34657
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:29.773701+00:00
-- url     : https://prove2.me/theorems/eb051916-f293-4efb-b6cf-d8319b167fb3
-- title:
--   A power of two modulo three
-- statement:
--   The remainder of $2^{2020}$ upon division by $3$ is
--
--   $$2^{2020}\bmod3=1.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34657` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34657; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_34657 :
  (2^2020) % 3 = 1  :=  by sorry
