-- Prove2me | Theorems.Thm_lean_workbook_plus_44792
-- name    : lean_workbook_plus_44792
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/89391778-436b-4e1c-af2e-aa011b5545fe
-- statement:
--   Find the general term of the sequence $U_{2^{2h}} = [2^{2h}\sqrt{2^{2h}}] = 2^{3h}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44792 (h : ℕ) : (2^(2 * h) * Real.sqrt ((2^(2 * h))) : ℝ) = 2^(3 * h)   :=  by sorry
