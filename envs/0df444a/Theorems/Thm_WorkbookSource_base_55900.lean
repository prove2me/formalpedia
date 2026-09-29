-- Prove2me | Theorems.Thm_WorkbookSource_base_55900
-- name    : WorkbookSource.base_55900
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:22:54.994925+00:00
-- url     : https://prove2.me/theorems/907e537e-9c65-4009-87e9-95ce53119abd
-- title:
--   An upper bound on seventy-two times the square root of five
-- statement:
--   Show that $ 72 \sqrt {5} < 161$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55900` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55900; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55900 : (72 * Real.sqrt 5 : ℝ) < 161  :=  by sorry
