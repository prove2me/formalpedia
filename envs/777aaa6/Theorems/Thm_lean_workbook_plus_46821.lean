-- Prove2me | Theorems.Thm_lean_workbook_plus_46821
-- name    : lean_workbook_plus_46821
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e82fa507-ed0c-43b4-bb9f-f72815df9045
-- statement:
--   Small: $\dbinom{7}{3}$\nMedium: $\dbinom{7}{4}$\nLarge: $\dbinom{7}{5}$\nTherefore the total is: $\dbinom{7}{3}+\dbinom{7}{4}+\dbinom{7}{5}=91$ , $\boxed{C}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46821 :
  (Nat.choose 7 3) + (Nat.choose 7 4) + (Nat.choose 7 5) = 91   :=  by sorry
