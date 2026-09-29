-- Prove2me | Theorems.Thm_lean_workbook_plus_72487
-- name    : lean_workbook_plus_72487
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/976b114b-b30a-4f87-bbe6-8c2a57307f8b
-- statement:
--   Prove that for all positive real numbers $a$, $a^3 + 2 \geq 3a$ using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72487 (a : ℝ) (ha : 0 < a) : a^3 + 2 ≥ 3*a   :=  by sorry
