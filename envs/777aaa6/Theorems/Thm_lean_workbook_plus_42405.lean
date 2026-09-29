-- Prove2me | Theorems.Thm_lean_workbook_plus_42405
-- name    : lean_workbook_plus_42405
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d71dd800-0491-4ac4-9166-8b27be2b34bd
-- statement:
--   Prove $ (x - z)^2 + (y - z)^2 \ge (x - z)(y - z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42405 (x y z: ℝ) : (x - z) ^ 2 + (y - z) ^ 2 ≥ (x - z) * (y - z)   :=  by sorry
