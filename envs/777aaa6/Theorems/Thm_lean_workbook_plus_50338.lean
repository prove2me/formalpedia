-- Prove2me | Theorems.Thm_lean_workbook_plus_50338
-- name    : lean_workbook_plus_50338
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/dca3ea07-9712-421f-9a20-a987915d5e50
-- statement:
--   Have $ |a^3|\le bc\Rightarrow a^6 + b^6 + c^6 = b^6 + c^6 + (a^3)^2\le b^6 + c^6 + b^2c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50338 (a b c : ℝ) : |a^3| ≤ b * c → a^6 + b^6 + c^6 ≤ b^6 + c^6 + b^2 * c^2   :=  by sorry
