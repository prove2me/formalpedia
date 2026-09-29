-- Prove2me | Theorems.Thm_lean_workbook_plus_46203
-- name    : lean_workbook_plus_46203
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/70930914-e50c-40e3-abd0-c7952e7f742e
-- statement:
--   =\\tfrac{\\sqrt5}{4}(1+\\tfrac14+\\tfrac1{16}+...)=\\tfrac{\\sqrt5}{4}\\cdot\\tfrac43=\\tfrac{\\sqrt5}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46203 :
  ∑' k : ℕ, (1 / 4)^k * (Real.sqrt 5 / 4) = (Real.sqrt 5 / 3)   :=  by sorry
