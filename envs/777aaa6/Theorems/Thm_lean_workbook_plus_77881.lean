-- Prove2me | Theorems.Thm_lean_workbook_plus_77881
-- name    : lean_workbook_plus_77881
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e75f2932-eacd-43be-9a80-9cdc0d4462a9
-- statement:
--   Determine the set of $(x, y)$ for which $k\pi + \frac{\pi}{6} < x-y < (k+1)\pi$ is satisfied.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77881 (x y : ℝ) (k : ℤ) : k * π + π / 6 < x - y ∧ x - y < (k + 1) * π ↔ k * π + π / 6 < x - y ∧ x - y < (k + 1) * π   :=  by sorry
