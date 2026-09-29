-- Prove2me | Theorems.Thm_WorkbookRestored_plus_26955
-- name    : WorkbookRestored.plus_26955
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:54.738269+00:00
-- url     : https://prove2.me/theorems/e9326272-7e3f-445d-8692-c0c107b9b3fe
-- title:
--   Lean-Workbook Plus 26955: Trigonometric identity
-- statement:
--   For every natural number $n$ and real $x$, $\sin^2(nx)=\tfrac12(1-\cos(2nx))$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_26955` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/cc40f7d7-d28d-45b9-8733-9dcece4f0554); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_26955; immutable original Prove2Me node cc40f7d7-d28d-45b9-8733-9dcece4f0554

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_26955 (n : ℕ) (x : ℝ) : (sin (n * x))^2 = 1 / 2 * (1 - cos (2 * n * x))   :=  by sorry
