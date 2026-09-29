-- Prove2me | Theorems.Thm_lean_workbook_plus_12113
-- name    : lean_workbook_plus_12113
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/171f89e0-fa37-4323-8d32-a698132d32ca
-- statement:
--   Prove that $\left(x^2-yz-1\right)^2+\left(y^2-zx-1\right)^2+\left(z^2-xy-1\right)^2\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12113 (x y z : ℝ) : (x^2 - y * z - 1)^2 + (y^2 - z * x - 1)^2 + (z^2 - x * y - 1)^2 ≥ 0   :=  by sorry
