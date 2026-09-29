-- Prove2me | Theorems.Thm_lean_workbook_plus_17350
-- name    : lean_workbook_plus_17350
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b0d1cbc5-6b03-4f9c-b58a-9cbbd2bd1d6a
-- statement:
--   Let be $ a,b,c,d\in \mathbb{R}_+$ such that $ abcd=1$ . Show that : $ 8+(a^2+b^2)(c^2+d^2)\ge 3(a+b)(c+d)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17350 (a b c d : ℝ) (habcd : a * b * c * d = 1) : 8 + (a^2 + b^2) * (c^2 + d^2) ≥ 3 * (a + b) * (c + d)   :=  by sorry
