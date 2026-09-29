-- Prove2me | Theorems.Thm_lean_workbook_plus_27037
-- name    : lean_workbook_plus_27037
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7d193d83-e033-44f3-9b37-f4748c2bc7aa
-- statement:
--   Solve the system of equations: \n$8 = A + B + C + D$ \n$16 = A + 2B + 4C + 8D$ \n$0 = A + 3B + 9C + 27D$ \n$-64 = A + 4B + 16C + 64D$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27037 (A B C D : ℝ) : (8 = A + B + C + D ∧ 16 = A + 2*B + 4*C + 8*D ∧ 0 = A + 3*B + 9*C + 27*D ∧ -64 = A + 4*B + 16*C + 64*D) ↔ A = 0 ∧ B = 0 ∧ C = 12 ∧ D = -4   :=  by sorry
