-- Prove2me | Theorems.Thm_lean_workbook_plus_80188
-- name    : lean_workbook_plus_80188
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/5bf8ee32-2c6b-4fd9-8d1c-80b4a216e6ff
-- statement:
--   $(a^2+b^2+c^2-ab-bc-ca)^2\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80188 (a b c: ℝ) : (a^2 + b^2 + c^2 - a * b - b * c - c * a)^2 ≥ 0   :=  by sorry
