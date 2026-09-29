-- Prove2me | Theorems.Thm_lean_workbook_plus_53893
-- name    : lean_workbook_plus_53893
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/016b3924-6efe-4683-ae1c-2df478d8901a
-- statement:
--   Find the solutions of $cos x \cdot cos(\frac{x}{2}) \cdot cos(\frac{3x}{2}) - sin x \cdot sin(\frac{x}{2}) \cdot sin(\frac{3x}{2}) = \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53893 : ∀ x : ℝ, (cos x * cos (x / 2) * cos (3 * x / 2) - sin x * sin (x / 2) * sin (3 * x / 2) = 1 / 2) ↔ x = π / 3 + 2 * π * ↑(Int.ofNat 0) ∨ x = π / 2 + 2 * π * ↑(Int.ofNat 0) ∨ x = 2 * π / 3 + 2 * π * ↑(Int.ofNat 0)   :=  by sorry
