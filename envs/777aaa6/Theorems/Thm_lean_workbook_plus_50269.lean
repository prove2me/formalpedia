-- Prove2me | Theorems.Thm_lean_workbook_plus_50269
-- name    : lean_workbook_plus_50269
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/06d229db-1693-46de-af7e-7b8d452dc89d
-- statement:
--   Prove that $b^2-bc+c^2\geq \frac{(b+c)^2}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50269 : ∀ b c : ℝ, b^2 - b*c + c^2 ≥ (b + c)^2 / 4   :=  by sorry
