-- Prove2me | Theorems.Thm_lean_workbook_plus_69223
-- name    : lean_workbook_plus_69223
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/994a1bce-46f6-47ee-8170-1e1c020efe0c
-- statement:
--   Or only use $x, y, z, v$ shows:\n\n$Q = \frac{1}{7}\,{\frac {M}{y{z}^{2}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69223 (M x y z v : ℝ) : M / (7 * y * z^2) = 1 / 7 * (M / (y * z^2))   :=  by sorry
