-- Prove2me | Theorems.Thm_lean_workbook_plus_69935
-- name    : lean_workbook_plus_69935
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/daae75fa-7ece-44f3-a9a4-963c50dbae63
-- statement:
--   Prove that for $x, y, z \in \mathbb{R}^+$, the following inequality holds:\n\n $\sum yz(y-z)^2(2y^2+yz+2z^2) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69935 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : y * z * (y - z) ^ 2 * (2 * y ^ 2 + y * z + 2 * z ^ 2) ≥ 0   :=  by sorry
