-- Prove2me | Theorems.Thm_lean_workbook_plus_6179
-- name    : lean_workbook_plus_6179
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0dc0a4c1-6a09-4b3f-aae6-a6c75cba7a4c
-- statement:
--   Prove the identity: $\sin 3\theta=3\sin \theta-4\sin ^ 3 \theta$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6179 (θ : ℝ) : sin (3 * θ) = 3 * sin θ - 4 * (sin θ)^3   :=  by sorry
