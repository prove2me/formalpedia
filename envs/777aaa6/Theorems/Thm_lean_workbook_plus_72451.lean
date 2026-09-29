-- Prove2me | Theorems.Thm_lean_workbook_plus_72451
-- name    : lean_workbook_plus_72451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/6a16a680-82c4-4c75-bba6-80bb5d82a225
-- statement:
--   We have : $\dfrac{1}{2-a }= \dfrac{a (a -1)^2}{2(2-a )} +\dfrac{1}{2}(a^2 +1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72451  (a : ℝ)
  (h₀ : a ≠ 2) :
  1 / (2 - a) = a * (a - 1)^2 / (2 * (2 - a)) + 1 / 2 * (a^2 + 1)   :=  by sorry
