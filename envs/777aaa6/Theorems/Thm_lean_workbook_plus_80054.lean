-- Prove2me | Theorems.Thm_lean_workbook_plus_80054
-- name    : lean_workbook_plus_80054
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/565167ed-00c4-41cf-a12f-a0db9b1a6a26
-- statement:
--   Using the Cauchy inequality, show that if $u+2v>4$, then $u^2+4v^2>8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80054 (u v : ℝ) (h : u + 2 * v > 4) : u ^ 2 + 4 * v ^ 2 > 8   :=  by sorry
