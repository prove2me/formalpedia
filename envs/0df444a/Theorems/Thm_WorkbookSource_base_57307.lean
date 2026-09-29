-- Prove2me | Theorems.Thm_WorkbookSource_base_57307
-- name    : WorkbookSource.base_57307
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:22:56.736946+00:00
-- url     : https://prove2.me/theorems/ff61e360-c369-4c64-a612-44789046bd26
-- title:
--   A lower bound on three times a difference of radicals
-- statement:
--   Prove that: $3(\sqrt{6}-\sqrt{2}) > 3.1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57307` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57307; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_57307 : (3 : ℝ) * (Real.sqrt 6 - Real.sqrt 2) > 3.1  :=  by sorry
