-- Prove2me | Theorems.Thm_lean_workbook_plus_43728
-- name    : lean_workbook_plus_43728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/94ecb513-406f-4425-8c0d-1985596182d7
-- statement:
--   Let $a,b,c\geq \frac{3}{2}.$ Prove that $a+2b+3c\geq \frac{9}{8}\left( \frac{1}{a}+ \frac{2}{b}+ \frac{3}{c}+4 \right) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43728 (a b c : ℝ) (ha : a ≥ 3 / 2) (hb : b ≥ 3 / 2) (hc : c ≥ 3 / 2) : a + 2 * b + 3 * c ≥ 9 / 8 * (1 / a + 2 / b + 3 / c + 4)   :=  by sorry
