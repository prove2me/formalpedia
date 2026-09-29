-- Prove2me | Theorems.Thm_lean_workbook_plus_19576
-- name    : lean_workbook_plus_19576
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/13dfb87a-5664-4692-83fb-506aa6c89f0e
-- statement:
--   3) $\tan x<0$ and so $\sin x$ and $\cos x$ are both nonzero with opposite signs.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19576 (x : ℝ) (hx : tan x < 0) : (sin x ≠ 0 ∧ cos x ≠ 0 ∧ sin x * cos x < 0)   :=  by sorry
