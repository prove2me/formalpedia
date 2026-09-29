-- Prove2me | Theorems.Thm_WorkbookSource_plus_78615
-- name    : WorkbookSource.plus_78615
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:23:29.20782+00:00
-- url     : https://prove2.me/theorems/af1e8b11-195c-4c39-a77e-90308616172c
-- title:
--   The twenty-ninth Mersenne number is composite
-- statement:
--   Prove that $2^{29}-1$ is not a prime number.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_78615` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_78615; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_78615 : ¬ Nat.Prime (2^29 - 1)   :=  by sorry
