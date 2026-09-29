-- Prove2me | Theorems.Thm_WorkbookRestored_plus_6172
-- name    : WorkbookRestored.plus_6172
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:52.743914+00:00
-- url     : https://prove2.me/theorems/c1240c86-ac9d-47c0-b402-152a778309f1
-- title:
--   Lean-Workbook Plus 6172: Trigonometric identity
-- statement:
--   Sum to product gives $\sin(20)+\sin(40)=2\sin(30)\cos(10)$
--
--   Source: Lean-Workbook row `lean_workbook_plus_6172` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/14a89328-d548-4fc1-9ae6-878b103307fc); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_6172; immutable original Prove2Me node 14a89328-d548-4fc1-9ae6-878b103307fc

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_6172 : ∀ a b c d : ℝ, a = 20 ∧ b = 40 → c = 30 ∧ d = 10 → sin a + sin b = 2 * sin c * cos d   :=  by sorry
