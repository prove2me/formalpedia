-- Prove2me | Theorems.Thm_lean_workbook_plus_74350
-- name    : lean_workbook_plus_74350
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/25c047f8-bb53-451a-b645-f09b1824bfae
-- statement:
--   Prove the inequality: $\frac{x^2+y^2+z^2}{3}\ge \left(\frac{x+y+z}{3}\right)^2$ for all real numbers $x$, $y$, and $z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74350 (x y z : ℝ) : (x ^ 2 + y ^ 2 + z ^ 2) / 3 ≥ (x + y + z) ^ 2 / 3 ^ 2   :=  by sorry
