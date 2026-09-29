-- Prove2me | Theorems.Thm_lean_workbook_plus_20732
-- name    : lean_workbook_plus_20732
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d7db0034-5218-484a-93ac-faf4d83cd274
-- statement:
--   What does $ \tan{\frac{\pi}{4}}$ equal in degrees?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20732 (x : ℝ) (hx : x = π / 4) : tan x = 1   :=  by sorry
