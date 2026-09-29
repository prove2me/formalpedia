-- Prove2me | Theorems.Thm_lean_workbook_plus_49960
-- name    : lean_workbook_plus_49960
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/dfa6256a-4bf5-470a-a528-0a27767ecc9c
-- statement:
--   Find the minimum of $\sqrt{x^{2}+y^{2}+z^{2}}$ if $x+y+z=13$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49960 (x y z : ℝ) (h : x + y + z = 13) :
 √(x^2 + y^2 + z^2) >= 5   :=  by sorry
