-- Prove2me | Theorems.Thm_lean_workbook_plus_75091
-- name    : lean_workbook_plus_75091
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e55fdc87-3e9c-4ca9-97b4-5de2c93a865f
-- statement:
--   Prove that $e^u \geq u + 1$ for $u > -1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75091 (u : ℝ) (h : u > -1) : exp u ≥ u + 1   :=  by sorry
