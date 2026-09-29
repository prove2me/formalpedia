-- Prove2me | Theorems.Thm_WorkbookRestored_plus_56140
-- name    : WorkbookRestored.plus_56140
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:07.607201+00:00
-- url     : https://prove2.me/theorems/7e8aeeb1-bf8a-4eb2-a8e8-0b4f37475f41
-- title:
--   Lean-Workbook Plus 56140: Trigonometric identity
-- statement:
--   For real $\alpha,\theta$, $(1+\cos\theta)(1+\cos\alpha)=4\cos^2(\theta/2)\cos^2(\alpha/2)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_56140` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/1c1d980e-94a9-4de6-a36c-d4cc5888bfea); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_56140; immutable original Prove2Me node 1c1d980e-94a9-4de6-a36c-d4cc5888bfea

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_56140 (α θ : ℝ) : (1 + Real.cos θ) * (1 + Real.cos α) = 4 * (Real.cos (θ / 2))^2 * (Real.cos (α / 2))^2   :=  by sorry
