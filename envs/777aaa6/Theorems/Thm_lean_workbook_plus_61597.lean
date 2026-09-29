-- Prove2me | Theorems.Thm_lean_workbook_plus_61597
-- name    : lean_workbook_plus_61597
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/16d72cf0-0a3f-43a1-8205-c7f8ee6df828
-- statement:
--   Prove that $x^3 + y^3 + z^3 \geq xy(x+y) + xz(x+z) + yz(y+z)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61597 : ∀ x y z : ℝ, x ^ 3 + y ^ 3 + z ^ 3 ≥ x * y * (x + y) + x * z * (x + z) + y * z * (y + z)   :=  by sorry
