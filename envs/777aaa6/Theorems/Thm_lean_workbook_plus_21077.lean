-- Prove2me | Theorems.Thm_lean_workbook_plus_21077
-- name    : lean_workbook_plus_21077
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/01e86855-388e-4827-88e6-47170d6b893e
-- statement:
--   $(a^2+nb^2)(c^2+nd^2) = (ac+nbd)^2 +n (ad-bc)^2$ ( Can also be written as ( $(ac-nbd)^2+n(ad+bc)^2$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21077 (a b c d n : ℤ) : (a^2 + n * b^2) * (c^2 + n * d^2) = (a * c + n * b * d)^2 + n * (a * d - b * c)^2   :=  by sorry
