-- Prove2me | Theorems.Thm_lean_workbook_plus_68439
-- name    : lean_workbook_plus_68439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4a6e3a2d-27b0-4d57-8143-d0b562e4eede
-- statement:
--   3(x^2+y^2+z^2) \ge (x+y+z)^2 so $x+y+z \le \sqrt{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68439 : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2)   :=  by sorry
