-- Prove2me | Theorems.Thm_lean_workbook_plus_12543
-- name    : lean_workbook_plus_12543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/858e977d-5c49-4cc1-a699-cfd853e4e2ef
-- statement:
--   Isn't the triangle inequality just for I z1 I + I z2 I $\ge$ I z1 + z2 I ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12543 (z1 z2 : ℂ) : ‖z1‖ + ‖z2‖ ≥ ‖z1 + z2‖   :=  by sorry
