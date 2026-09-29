-- Prove2me | Theorems.Thm_WorkbookRestored_plus_24031
-- name    : WorkbookRestored.plus_24031
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:10.715064+00:00
-- url     : https://prove2.me/theorems/c5deda68-2d7a-4857-a12b-0e3b17203760
-- title:
--   A power identity at exponents zero and one
-- statement:
--   For real $a$ and $x\in\{0,1\}$, $(1+a)^x=1+ax$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/4c910ee4-ad42-4d9a-923f-4163dcee487a), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_24031` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_24031; original Prove2Me node 4c910ee4-ad42-4d9a-923f-4163dcee487a; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_24031 (x : ℝ) (a : ℝ) (h : x = 0 ∨ x = 1) : (1 + a) ^ x = 1 + a * x   :=  by sorry
