-- Prove2me | Theorems.Thm_lean_workbook_plus_62196
-- name    : lean_workbook_plus_62196
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/d59eefc8-23b8-415b-a43d-698f50089fbc
-- statement:
--   Prove that $ x^2+y^2+z^2\ge xy+xz+yz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62196 : ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z   :=  by sorry
