-- Prove2me | Theorems.Thm_lean_workbook_plus_9294
-- name    : lean_workbook_plus_9294
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/706383cf-f3bf-49db-8f7b-b4a6a2bdc197
-- statement:
--   So $4x^3-3x-\frac 2{5\sqrt 5}=0$ and so $(\sqrt 5 x-2)(20x^2+8\sqrt 5 x+1)=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9294 :
  4 * x^3 - 3 * x - 2 / (5 * Real.sqrt 5) = 0 ↔ (Real.sqrt 5 * x - 2) * (20 * x^2 + 8 * Real.sqrt 5 * x + 1) = 0   :=  by sorry
