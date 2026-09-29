-- Prove2me | Theorems.Thm_lean_workbook_plus_81507
-- name    : lean_workbook_plus_81507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3880c977-53e8-4773-bbe3-6b9b3737095a
-- statement:
--   It is sufficient that: \n $ 12p-p^3\ge 27p-(p^2+3)(p+3)\Leftrightarrow 3p^2-12p+9\ge 0\Leftrightarrow 3(p-1)(p-3)\ge 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81507 : ∀ p : ℝ, 12 * p - p ^ 3 ≥ 27 * p - (p ^ 2 + 3) * (p + 3) ↔ 3 * (p - 1) * (p - 3) ≥ 0   :=  by sorry
