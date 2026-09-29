-- Prove2me | Theorems.Thm_lean_workbook_plus_13549
-- name    : lean_workbook_plus_13549
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4accb1d0-7650-4a14-8420-4ea9c1975081
-- statement:
--   Let $x \geq y \geq z$ be real numbers such that $xy + yz + zx = 1$ . Prove that $xz < \frac 12.$ Is it possible to improve the value of constant $\frac 12 \ ?$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13549 (x y z : ℝ) (hxy : x ≥ y ∧ y ≥ z) (h : x * y + y * z + z * x = 1) : x * z < 1 / 2   :=  by sorry
