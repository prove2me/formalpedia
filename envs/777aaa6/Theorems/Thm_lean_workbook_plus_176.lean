-- Prove2me | Theorems.Thm_lean_workbook_plus_176
-- name    : lean_workbook_plus_176
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/dcf2b26e-b8ae-478d-bd8e-8f508ddead25
-- statement:
--   Prove that $4s^2-21s+27\le 0$ for $\frac{9}{4}\le s\le 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_176 (s : ℝ) (hs : 9 / 4 ≤ s ∧ s ≤ 3) : 4 * s ^ 2 - 21 * s + 27 ≤ 0   :=  by sorry
