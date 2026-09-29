-- Prove2me | Theorems.Thm_lean_workbook_plus_37830
-- name    : lean_workbook_plus_37830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3e689d3a-1385-4ce0-97ee-bb8a05f607d0
-- statement:
--   Show that if $|x-4| < 1$ then $\frac{1}{|x+4|} \le \frac{1}{7}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37830 (x : ℝ) (hx : |x - 4| < 1) : 1 / |x + 4| ≤ 1 / 7   :=  by sorry
