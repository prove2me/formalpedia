-- Prove2me | Theorems.Thm_lean_workbook_plus_81742
-- name    : lean_workbook_plus_81742
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/cc08984b-77f6-45f3-8b30-a440698c0621
-- statement:
--   Prove that $(1 + a^2 + a^4)^4 \geq 9a^4(a + a^2 + a^3)^2$ for any real $a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81742 (a : ℝ) : (1 + a^2 + a^4)^4 ≥ 9 * a^4 * (a + a^2 + a^3)^2   :=  by sorry
