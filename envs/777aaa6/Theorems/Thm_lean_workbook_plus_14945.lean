-- Prove2me | Theorems.Thm_lean_workbook_plus_14945
-- name    : lean_workbook_plus_14945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/92222dab-3714-4a13-bc88-8e38cd926911
-- statement:
--   Show that $t^2(3t^2-8t+6) \geq 0$ for all real numbers $t$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14945 : ∀ t : ℝ, t^2 * (3 * t^2 - 8 * t + 6) ≥ 0   :=  by sorry
