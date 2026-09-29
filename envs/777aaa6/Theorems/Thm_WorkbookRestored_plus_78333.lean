-- Prove2me | Theorems.Thm_WorkbookRestored_plus_78333
-- name    : WorkbookRestored.plus_78333
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:41:45.8556+00:00
-- url     : https://prove2.me/theorems/a92f93c6-1fb7-4efc-b885-43fd80f67e7f
-- title:
--   Lean-Workbook Plus 78333: An affine angle has a unique value in the first quadrant
-- statement:
--   For $0<\theta<\pi/2$, there is exactly one $u\in(0,\pi/2)$ satisfying $u=(\theta+\pi)/3$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_78333` (Apache-2.0), [original record](https://prove2.me/theorems/738decfb-7be2-4891-a5ba-f51b1225f8ad). This repair only restores required imports and namespaces; the mathematical declaration is unchanged.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_78333; immutable original Prove2Me node 738decfb-7be2-4891-a5ba-f51b1225f8ad

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_78333 (n : ℕ) (θ_n : ℝ) (h₁ : 0 < θ_n ∧ θ_n < π/2) : ∃! θ_n1 : ℝ, θ_n1 = (θ_n + π)/3 ∧ 0 < θ_n1 ∧ θ_n1 < π/2   :=  by sorry
