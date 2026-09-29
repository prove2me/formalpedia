-- Prove2me | Theorems.Thm_lean_workbook_plus_31408
-- name    : lean_workbook_plus_31408
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/951dac85-a4f8-4a85-ba99-b07bce167abf
-- statement:
--   Prove that, if $z$ is a complex number and $n$ is a positive integer, then $\mid z^{n} \mid = \mid z \mid ^{n}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31408 (z : ℂ) (n : ℕ) : ‖z^n‖ = ‖z‖^n   :=  by sorry
