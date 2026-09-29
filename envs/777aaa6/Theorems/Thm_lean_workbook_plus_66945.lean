-- Prove2me | Theorems.Thm_lean_workbook_plus_66945
-- name    : lean_workbook_plus_66945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/b57a42c9-3047-4ef1-aac2-e83fbe86988a
-- statement:
--   Let $ a,b $ are positive real numbers such that $a^5+b^3\leq a^2+b^2. $ Prove that $a(a+b) \leq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66945 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^5 + b^3 ≤ a^2 + b^2) : a * (a + b) ≤ 2   :=  by sorry
