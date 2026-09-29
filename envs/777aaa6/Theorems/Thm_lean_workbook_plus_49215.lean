-- Prove2me | Theorems.Thm_lean_workbook_plus_49215
-- name    : lean_workbook_plus_49215
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fd9969b0-b797-4dca-912e-5707ea4fc9c9
-- statement:
--   Prove that:\n$\frac{a^{2}-b^{2}}{a^{2}+bc}+\frac{b^{2}-c^{2}}{b^{2}+ca}+\frac{c^{2}-a^{2}}{c^{2}+ab}\le 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49215 : ∀ a b c : ℝ, (a^2 - b^2) / (a^2 + b * c) + (b^2 - c^2) / (b^2 + c * a) + (c^2 - a^2) / (c^2 + a * b) ≤ 0   :=  by sorry
