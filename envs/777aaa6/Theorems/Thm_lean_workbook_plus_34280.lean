-- Prove2me | Theorems.Thm_lean_workbook_plus_34280
-- name    : lean_workbook_plus_34280
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/313704d3-c454-444b-a590-458d3fe00140
-- statement:
--   $ x-1=2k$ so $ x+1=2k+2$ ==> $ 8b=4k(k+1)$ ==> $ b=k(k+1)/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34280  (x b k : ℤ)
  (h₀ : x - 1 = 2 * k)
  (h₁ : x + 1 = 2 * k + 2)
  (h₂ : 8 * b = 4 * k * (k + 1)) :
  b = k * (k + 1) / 2   :=  by sorry
