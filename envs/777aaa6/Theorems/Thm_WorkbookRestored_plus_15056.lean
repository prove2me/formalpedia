-- Prove2me | Theorems.Thm_WorkbookRestored_plus_15056
-- name    : WorkbookRestored.plus_15056
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:43.898611+00:00
-- url     : https://prove2.me/theorems/c07dfdda-7d35-4809-a327-3f1d9fbdeb21
-- title:
--   Lean-Workbook Plus 15056: Trigonometric inequality
-- statement:
--   Prove that $0\le (1-\sin x)(1-\sin y)$
--
--   Source: Lean-Workbook row `lean_workbook_plus_15056` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/433665b4-664f-4aaf-ae6a-704048969a9c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_15056; immutable original Prove2Me node 433665b4-664f-4aaf-ae6a-704048969a9c

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_15056 : ∀ x y : ℝ, 0 ≤ (1 - Real.sin x) * (1 - Real.sin y)   :=  by sorry
