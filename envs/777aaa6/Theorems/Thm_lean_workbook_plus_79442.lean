-- Prove2me | Theorems.Thm_lean_workbook_plus_79442
-- name    : lean_workbook_plus_79442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/bcea32fa-1432-4685-afdb-453466636d37
-- statement:
--   Let $a,b,c\geq \frac{3}{2}.$ Prove that $a+2b+3c\geq \frac{27}{16}\left( \frac{1}{a}- \frac{2}{b}+ \frac{3}{c}+4 \right) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79442 (a b c : ℝ) (ha : 3 / 2 ≤ a) (hb : 3 / 2 ≤ b) (hc : 3 / 2 ≤ c) : a + 2 * b + 3 * c ≥ 27 / 16 * (1 / a - 2 / b + 3 / c + 4)   :=  by sorry
