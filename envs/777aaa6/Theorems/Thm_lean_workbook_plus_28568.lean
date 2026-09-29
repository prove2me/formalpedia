-- Prove2me | Theorems.Thm_lean_workbook_plus_28568
-- name    : lean_workbook_plus_28568
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7318052d-8526-4ae0-adca-241ecffcb274
-- statement:
--   Now, let $ n = - 8$ . Then, \n\n $ - 4B = 12$ \n\n $ B = - 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28568  (n B : ℤ)
  (h₀ : n = -8)
  (h₁ : -4 * B = 12) :
  B = -3   :=  by sorry
