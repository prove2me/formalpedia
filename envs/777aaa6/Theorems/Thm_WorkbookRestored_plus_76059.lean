-- Prove2me | Theorems.Thm_WorkbookRestored_plus_76059
-- name    : WorkbookRestored.plus_76059
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:27.097775+00:00
-- url     : https://prove2.me/theorems/a2f7cc90-f07e-4085-a79f-8606a6e81e71
-- title:
--   Lean-Workbook Plus 76059: The range of a real exponential with base above one
-- statement:
--   For real $b>1$, the range of $x\mapsto b^x$ is exactly $(0,\infty)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_76059` (Apache-2.0), [original record](https://prove2.me/theorems/c4969034-6e6e-4849-b054-5dde6cc9c1e1). This repair only restores required imports and namespaces; the mathematical declaration is unchanged.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_76059; immutable original Prove2Me node c4969034-6e6e-4849-b054-5dde6cc9c1e1

import Mathlib.Analysis.SpecialFunctions.Log.Base

theorem WorkbookRestored.plus_76059 (b : ℝ) (hb : 1 < b) : Set.range (λ x : ℝ => b^x) = Set.Ioi 0   :=  by sorry
