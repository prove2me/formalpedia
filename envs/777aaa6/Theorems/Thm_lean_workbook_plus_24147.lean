-- Prove2me | Theorems.Thm_lean_workbook_plus_24147
-- name    : lean_workbook_plus_24147
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f55e7ca7-dffd-4a58-bca8-e46afab01298
-- statement:
--   In the first equation, we have: \n $ 3x^2=23\implies x=\pm\sqrt{\frac{23}{3}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24147  (x : ℝ)
  (h₀ : 3 * x^2 = 23) :
  x = Real.sqrt (23 / 3) ∨ x = -Real.sqrt (23 / 3)   :=  by sorry
