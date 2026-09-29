-- Prove2me | Theorems.Thm_lean_workbook_plus_5725
-- name    : lean_workbook_plus_5725
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/c7ed210b-8c01-44e3-a3a9-17affb310bf0
-- statement:
--   $ \frac {y + z}{4yz} \ge \frac {1}{y + z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5725 (y z : ℝ) (hy : y > 0) (hz : z > 0) : (y + z) / (4 * y * z) ≥ 1 / (y + z)   :=  by sorry
