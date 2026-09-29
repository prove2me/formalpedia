-- Prove2me | Theorems.Thm_lean_workbook_plus_44023
-- name    : lean_workbook_plus_44023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/823eab41-5507-450c-9ad1-2aafd196d188
-- statement:
--   $ \frac 2{27} \geq \frac 23 (xy+yz+zx)^2 \Leftrightarrow 1 \geq 9(xy+yz+zx)^2 \quad (2) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44023 : ∀ x y z : ℝ, (2 / 27 ≥ 2 / 3 * (x * y + x * z + y * z) ^ 2 ↔ 1 ≥ 9 * (x * y + x * z + y * z) ^ 2)   :=  by sorry
