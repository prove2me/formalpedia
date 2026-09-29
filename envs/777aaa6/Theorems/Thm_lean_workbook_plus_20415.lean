-- Prove2me | Theorems.Thm_lean_workbook_plus_20415
-- name    : lean_workbook_plus_20415
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/abf36223-7a8f-4139-a28e-9e1edb727fed
-- statement:
--   Prove that $a^{2}b^{2}c^{2}+8(ab+bc+ac) \leq 25$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20415 : ∀ a b c : ℝ, a^2 * b^2 * c^2 + 8 * (a * b + b * c + a * c) ≤ 25   :=  by sorry
