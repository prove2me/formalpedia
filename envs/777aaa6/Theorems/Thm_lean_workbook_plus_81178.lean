-- Prove2me | Theorems.Thm_lean_workbook_plus_81178
-- name    : lean_workbook_plus_81178
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/15b450fd-036f-48d7-80ba-950449a66634
-- statement:
--   This is the case when $U$ is given by the full set $6x^2+3y^2-1\le 0\iff 2x^2+y^2\le 1/3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81178 (x y : ℝ) (hx: x ∈ Set.Icc (-1) 1) (hy: y ∈ Set.Icc (-1) 1) : 6 * x ^ 2 + 3 * y ^ 2 - 1 ≤ 0 ↔ 2 * x ^ 2 + y ^ 2 ≤ 1 / 3   :=  by sorry
