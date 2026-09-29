-- Prove2me | Theorems.Thm_lean_workbook_plus_35923
-- name    : lean_workbook_plus_35923
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/cc41575f-ef1d-4586-a10e-b7f554f1fecb
-- statement:
--   Why does $\frac{a}{b} = \frac{c}{d}$ mean $ad = bc$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35923 (a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = b * c   :=  by sorry
