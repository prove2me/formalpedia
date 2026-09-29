-- Prove2me | Theorems.Thm_lean_workbook_plus_69493
-- name    : lean_workbook_plus_69493
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/37cf9f5f-3278-4cde-9758-443939d84a9e
-- statement:
--   For $n=2$ , we have $1 = \lfloor \frac{2}{2} \rfloor \le m \le 2-1 =1 $ then $m=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69493  (m : ℕ)
  (h₀ : 1 ≤ m)
  (h₁ : m ≤ 2 - 1) :
  m = 1   :=  by sorry
