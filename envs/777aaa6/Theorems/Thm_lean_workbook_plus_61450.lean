-- Prove2me | Theorems.Thm_lean_workbook_plus_61450
-- name    : lean_workbook_plus_61450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b4dbe84c-37fc-4899-91a3-188d689212bf
-- statement:
--   Let $ a,b>0 $ and $ \dfrac{1}{a^2+1}+\dfrac{2}{b^2+1}=1. $ Prove that $a(4b-a) \leq 6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61450 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / (a^2 + 1) + 2 / (b^2 + 1) = 1) : a * (4 * b - a) ≤ 6   :=  by sorry
