-- Prove2me | Theorems.Thm_lean_workbook_plus_24620
-- name    : lean_workbook_plus_24620
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d9307660-8872-4d34-8b9e-525f0dff0bd9
-- statement:
--   Prove that $3u^4+2u^3v-3u^2v^2-2uv^3+3v^4\ge 0$ for non-negative $u$ and $v$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24620 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 3 * u ^ 4 + 2 * u ^ 3 * v - 3 * u ^ 2 * v ^ 2 - 2 * u * v ^ 3 + 3 * v ^ 4 ≥ 0   :=  by sorry
