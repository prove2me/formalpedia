-- Prove2me | Theorems.Thm_WorkbookRestored_plus_31177
-- name    : WorkbookRestored.plus_31177
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:26.755685+00:00
-- url     : https://prove2.me/theorems/a4b90c1e-ace7-4b07-af59-47028d7e89b6
-- title:
--   Lean-Workbook Plus 31177: Trigonometric inequality
-- statement:
--   For $x,y\in[0,\pi]$, $\sin((x+y)/2)\cos((x-y)/2)\le\sin((x+y)/2)$. This is the inequality component of the source’s sum-to-product statement.
--
--   Source: Lean-Workbook row `lean_workbook_plus_31177` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/06d3a222-d5f5-452d-8975-70af7c7f723f); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_31177; immutable original Prove2Me node 06d3a222-d5f5-452d-8975-70af7c7f723f

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_31177 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ π) (hy : 0 ≤ y ∧ y ≤ π) :
  sin ((x + y) / 2) * cos ((x - y) / 2) ≤ sin ((x + y) / 2)   :=  by sorry
