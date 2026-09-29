-- Prove2me | Theorems.Thm_lean_workbook_plus_47050
-- name    : lean_workbook_plus_47050
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d43c5cc0-bc1a-4b1f-9a12-7f7ffed56a51
-- statement:
--   For each positive number $a$ , prove that its multiplicative inverse $a^{-1}$ is also positive.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47050 (a : ℝ) (ha : 0 < a) : 0 < a⁻¹   :=  by sorry
