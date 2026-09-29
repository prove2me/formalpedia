-- Prove2me | Theorems.Thm_lean_workbook_plus_37513
-- name    : lean_workbook_plus_37513
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a4e9c7c0-c31e-4057-b72e-9fde342163a7
-- statement:
--   Prove that $3\left( xy+yz+zx\right) \leq \left( x+y+z\right) ^{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37513 : ∀ x y z : ℝ, 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2   :=  by sorry
