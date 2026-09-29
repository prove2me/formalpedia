-- Prove2me | Theorems.Thm_lean_workbook_plus_33271
-- name    : lean_workbook_plus_33271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2341f057-8802-4e0a-8251-8efe51334f4c
-- statement:
--   Let $a,b,c \le 0$ . Prove that \n\n $$\max(a,c)+\max(b,c) \le \max(a+b, c)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33271 (a b c : ℝ) (hab : a ≤ 0) (hbc : b ≤ 0) (hca : c ≤ 0) : max a c + max b c ≤ max (a + b) c   :=  by sorry
