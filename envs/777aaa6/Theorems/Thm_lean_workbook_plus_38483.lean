-- Prove2me | Theorems.Thm_lean_workbook_plus_38483
-- name    : lean_workbook_plus_38483
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/edeeb5cb-58fd-4805-879b-a5576ffb0308
-- statement:
--   If there is exactly 1 ball, then there are $\binom11\binom94$ ways to do this, which gives a probability of: $\frac{\binom11\binom94}{\binom{10}1\binom{9}4}=\frac1{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38483 (Nat.choose 1 1 * Nat.choose 9 4)/(Nat.choose 10 1 * Nat.choose 9 4) = 1/10   :=  by sorry
