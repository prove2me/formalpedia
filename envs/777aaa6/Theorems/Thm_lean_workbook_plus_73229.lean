-- Prove2me | Theorems.Thm_lean_workbook_plus_73229
-- name    : lean_workbook_plus_73229
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/100140e0-72ea-4946-b292-adf01f54ea07
-- statement:
--   Show that the expression $3u^2 - 6u$ is greater than or equal to 0 for $u \geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73229 (u : ℝ) (h : u ≥ 2) : 3 * u ^ 2 - 6 * u ≥ 0   :=  by sorry
