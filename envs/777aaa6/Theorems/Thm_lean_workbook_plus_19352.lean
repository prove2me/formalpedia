-- Prove2me | Theorems.Thm_lean_workbook_plus_19352
-- name    : lean_workbook_plus_19352
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/3c936e50-d540-463b-8a68-730eae681f17
-- statement:
--   In general, if $a$ divides $b$ , then $x^a - 1$ divides $x^b - 1$ . If $a$ divides $b$ , there exists an integer $k$ such that $ka = b$ , so $x^{ka} - 1 = (x^a-1)\left(\displaystyle\sum_{i=0}^{k-1}x^{ia}\right)$ . Therefore, $x^a - 1$ divides $x^ka - 1$ , so $x^a - 1$ divides $x^b-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19352  (a b : ℕ)
  (h₀ : a ∣ b) :
  (x^a - 1) ∣ (x^b - 1)   :=  by sorry
