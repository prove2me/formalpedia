-- Prove2me | Theorems.Thm_lean_workbook_plus_82692
-- name    : lean_workbook_plus_82692
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/79e147a9-f635-48f4-b1da-3bede38a3892
-- statement:
--   Prove that for all $a > 0$, the inequality $\frac{a^4+9}{10a} > \frac{4}{5}$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82692 (a : ℝ) (ha : 0 < a) : (a^4 + 9) / (10*a) > 4/5   :=  by sorry
