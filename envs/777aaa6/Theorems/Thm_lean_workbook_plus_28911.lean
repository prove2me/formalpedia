-- Prove2me | Theorems.Thm_lean_workbook_plus_28911
-- name    : lean_workbook_plus_28911
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/5da15d33-6d66-4ca1-b947-367c071c45c3
-- statement:
--   $2S = A+B+9+C+D+12 = 144$ , once that $A+B+C+D = 123$ . This give us that $S = 72$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28911  (a b c d s : ℕ)
  (h₀ : a + b + c + d = 123)
  (h₁ : 2 * s = a + b + 9 + c + d + 12) :
  s = 72   :=  by sorry
