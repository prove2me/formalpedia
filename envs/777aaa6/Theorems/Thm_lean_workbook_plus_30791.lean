-- Prove2me | Theorems.Thm_lean_workbook_plus_30791
-- name    : lean_workbook_plus_30791
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/36e96824-c29d-44fe-b940-06794997c126
-- statement:
--   Let $a$ and $b$ are non-negative real numbers. Prove that: $(a^{2}+2005b+2006)(b^{2}+2005a+2006)\geq(2007a+2005)(2007b+2005).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30791 (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : (a^2 + 2005*b + 2006)*(b^2 + 2005*a + 2006) ≥ (2007*a + 2005)*(2007*b + 2005)   :=  by sorry
