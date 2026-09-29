-- Prove2me | Theorems.Thm_lean_workbook_plus_14089
-- name    : lean_workbook_plus_14089
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a8c28f94-dcc6-4f3c-8208-2146be26388d
-- statement:
--   Prove that $2\sin(\alpha)^2+2\sin(\beta)^2+2 \geq 2\sin(\alpha)+2\sin(\beta)+2\sin(\alpha)\sin(\beta)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14089 (α β : ℝ) : 2 * sin α ^ 2 + 2 * sin β ^ 2 + 2 ≥ 2 * sin α + 2 * sin β + 2 * sin α * sin β   :=  by sorry
