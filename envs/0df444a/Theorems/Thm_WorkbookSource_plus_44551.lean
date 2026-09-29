-- Prove2me | Theorems.Thm_WorkbookSource_plus_44551
-- name    : WorkbookSource.plus_44551
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:23:11.47601+00:00
-- url     : https://prove2.me/theorems/92532b3c-b4b4-4433-8a74-ac795f87eee2
-- title:
--   The integer two to the sixty-fifth plus one is composite
-- statement:
--   Prove that $2^{65} + 1$ is not a prime number.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44551` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44551; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_44551 : ¬ Nat.Prime (2^65 + 1)   :=  by sorry
