-- Prove2me | Theorems.Thm_lean_workbook_plus_29652
-- name    : lean_workbook_plus_29652
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/99ef0b92-e627-48d9-a7a7-b7c1ba105f05
-- statement:
--   Summing these values ( $64+80+24+2=170$ ) and multiplying by $3$ , we get $170*3=510$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29652  (h₀ : x = 64)
  (h₁ : y = 80)
  (h₂ : z = 24)
  (h₃ : a = 2) :
  3 * (x + y + z + a) = 510   :=  by sorry
