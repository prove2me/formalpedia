-- Prove2me | Theorems.Thm_lean_workbook_plus_62954
-- name    : lean_workbook_plus_62954
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8e6baa5f-ed87-4169-b4bc-0b051fc170e1
-- statement:
--   Which is AM-GM: $\frac{x+(y+z+t)}{2} \geq \sqrt{x(y+z+t)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62954 : ∀ x y z t : ℝ, (x + (y + z + t)) / 2 ≥ Real.sqrt (x * (y + z + t))   :=  by sorry
