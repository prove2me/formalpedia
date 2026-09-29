-- Prove2me | Theorems.Thm_lean_workbook_plus_42808
-- name    : lean_workbook_plus_42808
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fc23e06a-e589-4380-bfca-4651e2ff8bda
-- statement:
--   $ \dfrac{1}{4}<x$ is the same as $ x>\dfrac{1}{4}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42808 (x : ℝ) : 1 / 4 < x ↔ x > 1 / 4   :=  by sorry
