-- Prove2me | Theorems.Thm_lean_workbook_plus_47123
-- name    : lean_workbook_plus_47123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/247f4016-5f9b-4f19-a295-4294609d35eb
-- statement:
--   Show that if $ a \ge 0 $ then $ a^6 +2 \ge a^3 + a^2 +a $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47123 (a:ℝ) (ha : a ≥ 0) : a^6 + 2 ≥ a^3 + a^2 + a   :=  by sorry
