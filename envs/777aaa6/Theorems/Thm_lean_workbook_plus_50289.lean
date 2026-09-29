-- Prove2me | Theorems.Thm_lean_workbook_plus_50289
-- name    : lean_workbook_plus_50289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f88fb2f1-e4ad-4fef-9f57-9c3cfc6904c6
-- statement:
--   Given $b=-a\frac{p^4+1}{p^3}$ and $c=\frac{a}{p^2}$, prove $(a^2+c^2)^2=ab^2c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50289 (a b c : ℝ) (p : ℝ) (hp : p ≠ 0) (hbc : b = -a * (p^4 + 1) / p^3) (hcc : c = a / p^2) : (a^2 + c^2)^2 = a * b^2 * c   :=  by sorry
