-- Prove2me | Theorems.Thm_lean_workbook_plus_70266
-- name    : lean_workbook_plus_70266
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/8b7114ae-c985-446f-a9cd-23555d0bbbc4
-- statement:
--   But $90\geq b^2+4^2+6^2 \Rightarrow b \leq \sqrt{38}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70266 (b : ℝ) : 90 ≥ b^2 + 4^2 + 6^2 → b ≤ Real.sqrt 38   :=  by sorry
