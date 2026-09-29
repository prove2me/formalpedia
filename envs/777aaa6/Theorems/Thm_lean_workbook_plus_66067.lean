-- Prove2me | Theorems.Thm_lean_workbook_plus_66067
-- name    : lean_workbook_plus_66067
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c9601331-bb25-478c-b313-3193585e73f0
-- statement:
--   Prove that $b^3+c^3+8-6bc\ge0$ for $c,b \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66067 (b c : ℝ) (hb : b ≥ 0) (hc : c ≥ 0): b^3 + c^3 + 8 - 6 * b * c ≥ 0   :=  by sorry
