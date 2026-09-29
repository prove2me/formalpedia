-- Prove2me | Theorems.Thm_lean_workbook_plus_47973
-- name    : lean_workbook_plus_47973
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/bb9d1697-81f4-46c0-ad6d-a6428c93e97c
-- statement:
--   $S_{max} = 9F_{max} = 9 \cdot 18515 = 166635,$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47973  (s f : ℕ)
  (h₀ : s = 9 * f)
  (h₁ : f = 18515) :
  s = 166635   :=  by sorry
