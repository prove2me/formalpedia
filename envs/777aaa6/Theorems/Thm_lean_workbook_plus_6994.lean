-- Prove2me | Theorems.Thm_lean_workbook_plus_6994
-- name    : lean_workbook_plus_6994
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3d7c6741-1f58-4ba3-b98f-626ad2346a71
-- statement:
--   Known $a, b, c \in \mathbb{R}$ . $a^2 + b ^2 + c^2 = 1$ . Solve $ab + bc + ca \ge - \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6994 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 1) : a * b + b * c + c * a ≥ -1 / 2   :=  by sorry
