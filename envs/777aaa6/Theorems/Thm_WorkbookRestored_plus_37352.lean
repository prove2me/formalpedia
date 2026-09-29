-- Prove2me | Theorems.Thm_WorkbookRestored_plus_37352
-- name    : WorkbookRestored.plus_37352
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:15.231133+00:00
-- url     : https://prove2.me/theorems/93bcc915-222c-400e-8e56-1af50d573d77
-- title:
--   Lean-Workbook Plus 37352: Trigonometric inequality
-- statement:
--   For every $\varepsilon>0$, there is $\delta>0$ such that $x\ne0$ and $|x|<\delta$ imply $|x\sin(1/x)|<\varepsilon$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_37352` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/1da4a1e0-e008-4e55-8291-a429ff0cc666); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_37352; immutable original Prove2Me node 1da4a1e0-e008-4e55-8291-a429ff0cc666

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_37352 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ≠ 0 ∧ |x| < δ → |x * sin (1/x)| < ε   :=  by sorry
