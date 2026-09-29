-- Prove2me | Theorems.Thm_WorkbookRestored_plus_738
-- name    : WorkbookRestored.plus_738
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:03:03.388789+00:00
-- url     : https://prove2.me/theorems/45f43aec-b267-4b3d-b41b-36dd1c95b650
-- title:
--   Recovering a logarithm from a linear relation
-- statement:
--   Let $r$ be real. If $\log5=r\log2$, then
--
--   $$r=\log_2 5.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_738` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `25110978-ff41-4f3e-9a23-51425715a12b`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_738; original Prove2Me theorem ID 25110978-ff41-4f3e-9a23-51425715a12b; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_738  (r : ℝ)
  (h₀ : Real.log 5 = r * Real.log 2) :
  r = Real.logb 2 5   :=  by sorry
