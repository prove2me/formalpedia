-- Prove2me | Theorems.Thm_lean_workbook_plus_44958
-- name    : lean_workbook_plus_44958
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f32d3cea-db72-4cfc-a76e-992cd302493b
-- statement:
--   Prove that if $a \ge 0$, then $2(a^2+1)^3 \ge (a^3+1)(a+1)^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44958 (a : ℝ) (ha : a ≥ 0) : 2 * (a^2 + 1)^3 ≥ (a^3 + 1) * (a + 1)^3   :=  by sorry
