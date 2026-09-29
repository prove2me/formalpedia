-- Prove2me | Theorems.Thm_lean_workbook_plus_65585
-- name    : lean_workbook_plus_65585
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6f4c31a8-5457-4fd7-afbf-48c91cf37006
-- statement:
--   $-\arcsin \frac 15-\arcsin \frac 45 + (2k+1)\pi$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65585 (k : ℤ) : -arcsin (1/5) - arcsin (4/5) + (2 * k + 1) * π = -arcsin (1/5) - arcsin (4/5) + (2 * k + 1) * π   :=  by sorry
