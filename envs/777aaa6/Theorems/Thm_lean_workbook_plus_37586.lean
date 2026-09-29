-- Prove2me | Theorems.Thm_lean_workbook_plus_37586
-- name    : lean_workbook_plus_37586
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d1116624-a0f8-4a7d-bf98-06034376bf9c
-- statement:
--   Let $a,b,c\geq 0$ and $a^3+b^3+c^3+3abc=6$ . Prove that \n $ 5(a+b+c) \geq 9+6abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37586 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) (h : a^3 + b^3 + c^3 + 3 * a * b * c = 6) : 5 * (a + b + c) ≥ 9 + 6 * a * b * c   :=  by sorry
