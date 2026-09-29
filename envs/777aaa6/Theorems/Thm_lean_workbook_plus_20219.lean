-- Prove2me | Theorems.Thm_lean_workbook_plus_20219
-- name    : lean_workbook_plus_20219
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/559b2279-5e89-44bc-8056-56c60bf9c0ea
-- statement:
--   If $x, y, z \in \mathbb{R}$, then prove that $(xy)^2 + (yz)^2 + (zx)^2 \geq (x + y + z)xyz$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20219 (x y z : ℝ) : (x * y) ^ 2 + (y * z) ^ 2 + (z * x) ^ 2 ≥ (x + y + z) * x * y * z   :=  by sorry
