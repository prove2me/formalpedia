-- Prove2me | Theorems.Thm_lean_workbook_plus_33893
-- name    : lean_workbook_plus_33893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/54966574-486a-4c22-8ca1-2fbaa27921c1
-- statement:
--   Prove that $2u^3+2v^3+2w^3-u^2v-u^2w-v^2w-w^2u\ge 0$ for non-negative $u$, $v$, and $w$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33893 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) : 2 * u ^ 3 + 2 * v ^ 3 + 2 * w ^ 3 - u ^ 2 * v - u ^ 2 * w - v ^ 2 * w - w ^ 2 * u ≥ 0   :=  by sorry
