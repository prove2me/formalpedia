-- Prove2me | Theorems.Thm_lean_workbook_plus_8132
-- name    : lean_workbook_plus_8132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/51292f6a-d59f-461a-b9b6-48644e36baf4
-- statement:
--   Not as nice but.. $ x+y+z \ge xyz \Longrightarrow \frac{1}{yz}+ \frac{1}{zx}+ \frac{1}{xy}\ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8132 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : x + y + z >= x*y*z → 1/(x*y) + 1/(y*z) + 1/(x*z) >= 1   :=  by sorry
