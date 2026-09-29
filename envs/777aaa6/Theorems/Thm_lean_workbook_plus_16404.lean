-- Prove2me | Theorems.Thm_lean_workbook_plus_16404
-- name    : lean_workbook_plus_16404
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/aca7f14b-2eac-4454-b46a-be68da299380
-- statement:
--   Find $\sin2x$ if $\cos x+\sin x=\tfrac{6}{5}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16404 (x : ℝ) (hx : cos x + sin x = 6 / 5) : sin (2 * x) = 12 / 25   :=  by sorry
