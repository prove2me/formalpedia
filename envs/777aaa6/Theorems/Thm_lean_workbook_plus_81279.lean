-- Prove2me | Theorems.Thm_lean_workbook_plus_81279
-- name    : lean_workbook_plus_81279
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c779acd0-994d-44de-8cc5-ec821491dbfc
-- statement:
--   Derive the equation $2s=3b$ from the relationship $s={111\over 20}r=3(s-b)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81279 (s b r : ℝ) : s = 111 / 20 * r ∧ s = 3 * (s - b) → 2 * s = 3 * b   :=  by sorry
