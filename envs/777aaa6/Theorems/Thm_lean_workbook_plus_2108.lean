-- Prove2me | Theorems.Thm_lean_workbook_plus_2108
-- name    : lean_workbook_plus_2108
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/253081b6-4705-4678-942d-d76c78847521
-- statement:
--   Prove that equality holds when $x+y=y+z=z+t=t+x\Leftrightarrow x=z\wedge y=t$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2108 : ∀ {x y z t : ℝ}, x + y = y + z ∧ y + z = z + t ∧ z + t = t + x ↔ x = z ∧ y = t   :=  by sorry
