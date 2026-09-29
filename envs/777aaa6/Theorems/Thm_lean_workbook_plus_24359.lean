-- Prove2me | Theorems.Thm_lean_workbook_plus_24359
-- name    : lean_workbook_plus_24359
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2e21f383-0cd9-4a09-97ad-370e3898c0dd
-- statement:
--   If $a \in \mathbb R+$, prove that there is a perfect square in $[a^2,(a+1)^2]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24359 (a : ℝ) (ha : 0 < a) : ∃ x, x^2 ∈ Set.Icc (a^2) ((a + 1)^2)   :=  by sorry
