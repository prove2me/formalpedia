-- Prove2me | Theorems.Thm_lean_workbook_plus_24996
-- name    : lean_workbook_plus_24996
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/96108a58-3016-4a0f-b386-e692301a4de5
-- statement:
--   Prove that if there exists a function $ g: Y\to X$ such that $ f\circ g = I_{Y}$, then $ f$ is a surjection.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24996 {X Y: Type} {f : X → Y} (g : Y → X) (h₁ : f ∘ g = id) : Function.Surjective f   :=  by sorry
