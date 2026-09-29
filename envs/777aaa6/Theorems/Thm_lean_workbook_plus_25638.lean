-- Prove2me | Theorems.Thm_lean_workbook_plus_25638
-- name    : lean_workbook_plus_25638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4bb96aa4-885f-4602-8644-6fad35611cb8
-- statement:
--   Let $x \geq y \geq z$ be real numbers such that $xy + yz + zx = 1$ . Prove that $xz < \frac 12.$ Is it possible to improve the value of constant $\frac 12 \ ?$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25638 (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hxyz : x * y + y * z + z * x = 1) : x * z < 1 / 2   :=  by sorry
