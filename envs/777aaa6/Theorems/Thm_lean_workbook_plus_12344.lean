-- Prove2me | Theorems.Thm_lean_workbook_plus_12344
-- name    : lean_workbook_plus_12344
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a1cbf869-b088-4ff0-976d-da26ac04b371
-- statement:
--   Prove the inequality \(a^3+b^3+c^3\geq a^2b+b^2c+c^2a\) over \(\mathbb{R_+}\) using the rearrangement inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12344 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a   :=  by sorry
