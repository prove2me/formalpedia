-- Prove2me | Theorems.Thm_lean_workbook_plus_40868
-- name    : lean_workbook_plus_40868
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b2b01199-d35f-4718-8eb3-322c8aa0bb43
-- statement:
--   prove that: $5.3+y^2x^2+y^2z^2+z^2x^2 \geq 2(xy+zx+yz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40868 (x y z : ℝ) : 5.3 + y^2 * x^2 + y^2 * z^2 + z^2 * x^2 ≥ 2 * (x * y + z * x + y * z)   :=  by sorry
