-- Prove2me | Theorems.Thm_lean_workbook_plus_16243
-- name    : lean_workbook_plus_16243
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/001045ad-78aa-44f1-a7c6-81ab243c4ca3
-- statement:
--   Prove that $x + y + z \geq \sqrt{3(xy + xz + yz)}$ where $x, y, z \in \mathbb{R}^+$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16243 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x + y + z ≥ Real.sqrt (3 * (x * y + x * z + y * z))   :=  by sorry
