-- Prove2me | Theorems.Thm_WorkbookSource_plus_76773
-- name    : WorkbookSource.plus_76773
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:23:27.425202+00:00
-- url     : https://prove2.me/theorems/6e9f4984-acf2-4e1f-8a8c-98b242626e3f
-- title:
--   The thirty-seventh Mersenne number is composite
-- statement:
--   Prove that $2^{37} -1 = 137438953471$ is not a prime.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76773` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76773; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_76773 : ¬ (2^37 - 1).Prime   :=  by sorry
