-- Prove2me | Theorems.Thm_lean_workbook_plus_27328
-- name    : lean_workbook_plus_27328
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2899eacb-af03-49da-a3f1-c305f73092c5
-- statement:
--   Let $ a,b,c,d$ be real numbers, such that $ a^2\le 1, a^2 + b^2\le 5, a^2 + b^2 + c^2\le 14, a^2 + b^2 + c^2 + d^2\le 30$ . Prove that $ a + b + c + d\le 10$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27328 (a b c d : ℝ) (ha : a ^ 2 ≤ 1) (hb : a ^ 2 + b ^ 2 ≤ 5) (hc : a ^ 2 + b ^ 2 + c ^ 2 ≤ 14) (hd : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 30) : a + b + c + d ≤ 10   :=  by sorry
