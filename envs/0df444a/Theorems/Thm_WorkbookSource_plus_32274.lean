-- Prove2me | Theorems.Thm_WorkbookSource_plus_32274
-- name    : WorkbookSource.plus_32274
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:23:13.512344+00:00
-- url     : https://prove2.me/theorems/18aece9a-4cd1-4529-aaa1-1b7990686629
-- title:
--   The fifth Fermat number is composite
-- statement:
--   Prove that $2^{32} + 1$ is not a prime number. (no calculators allowed)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_32274` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_32274; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_32274 : ¬Nat.Prime (2^32 + 1)   :=  by sorry
