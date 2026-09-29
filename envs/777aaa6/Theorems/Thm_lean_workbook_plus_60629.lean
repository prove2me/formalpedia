-- Prove2me | Theorems.Thm_lean_workbook_plus_60629
-- name    : lean_workbook_plus_60629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e47753d1-0adf-4362-98ba-0a2a89892691
-- statement:
--   Prove that: $(\sqrt{x} - 1)^2 + (\sqrt{y} - 1)^2 \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60629 (x y : ℝ) : (Real.sqrt x - 1) ^ 2 + (Real.sqrt y - 1) ^ 2 ≥ 0   :=  by sorry
