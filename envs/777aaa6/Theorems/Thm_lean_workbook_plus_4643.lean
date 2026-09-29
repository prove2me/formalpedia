-- Prove2me | Theorems.Thm_lean_workbook_plus_4643
-- name    : lean_workbook_plus_4643
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/98eaf44b-34e4-4b55-8ecc-7896cc963976
-- statement:
--   Let $a,b $ be real numbers such that $ a^2(a+1)+b^2(b+1)=4 $ . Prove that\n $$ a+b\leq 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4643 (a b : ℝ) (h : a^2 * (a + 1) + b^2 * (b + 1) = 4) : a + b ≤ 2   :=  by sorry
