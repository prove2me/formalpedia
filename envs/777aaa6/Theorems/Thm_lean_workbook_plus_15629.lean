-- Prove2me | Theorems.Thm_lean_workbook_plus_15629
-- name    : lean_workbook_plus_15629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/88931bfe-bbaa-4f1b-b8f5-a8a2dff4c7eb
-- statement:
--   Let $xyz = a^3$ \nfrom the condition we have $4\ge a^3+3a^2$ \nThen, $(a-1)(a+2)^2\le 0 $ \nSo, $ a\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15629  (x y z a : ℝ)
  (h₀ : x*y*z = a^3)
  (h₁ : 4 ≥ a^3 + 3*a^2) :
  a ≤ 1   :=  by sorry
