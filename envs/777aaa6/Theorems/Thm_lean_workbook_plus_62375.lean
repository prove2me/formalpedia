-- Prove2me | Theorems.Thm_lean_workbook_plus_62375
-- name    : lean_workbook_plus_62375
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/5ba07afe-e9bc-45bc-baef-5bf40ff0818b
-- statement:
--   $c = a+\frac{a^2}{b}$ and $d = b+\frac{b^2}{a}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62375 (a b c d : ℝ) : c = a + a^2 / b ∧ d = b + b^2 / a ↔ c = a + a^2 / b ∧ d = b + b^2 / a   :=  by sorry
