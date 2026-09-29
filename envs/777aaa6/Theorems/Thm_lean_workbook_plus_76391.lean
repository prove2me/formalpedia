-- Prove2me | Theorems.Thm_lean_workbook_plus_76391
-- name    : lean_workbook_plus_76391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9abf2fa2-b5dd-4572-8690-ec487c80f325
-- statement:
--   Let $a=\frac{3}{x}$ , $b=\frac{3}{y}$ and $c=\frac{3}{z}$ , where $x$ , $y$ and $z$ are positives.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76391 (a b c x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : a = 3 / x ∧ b = 3 / y ∧ c = 3 / z → a + b + c = 3 / x + 3 / y + 3 / z   :=  by sorry
