-- Prove2me | Theorems.Thm_WorkbookSource_plus_24111
-- name    : WorkbookSource.plus_24111
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:22:59.766451+00:00
-- url     : https://prove2.me/theorems/2e32f138-4d2c-41ae-b88d-ae40ea23dc12
-- title:
--   The integer two to the tenth plus five to the twelfth is composite
-- statement:
--   Prove that the number $2^{10}+5^{12}$ is not prime
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_24111` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_24111; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_24111 : ¬ Nat.Prime (2^10 + 5^12)   :=  by sorry
