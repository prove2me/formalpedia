-- Prove2me | Theorems.Thm_lean_workbook_plus_21844
-- name    : lean_workbook_plus_21844
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d69a3b94-83b3-41d1-87dc-03da94d465f6
-- statement:
--   So...if the values are in cents...to convert them to dollars would be... $ 10^{ - 2}(x + y + z + w) = 7.11$ and $ (10^{ - 2}x)(10^{ - 2}y)(10^{ - 2}z)(10^{ - 2}w) = 7.11\Leftrightarrow$ $ (10^{ - 8})xyzw = 7.11\Leftrightarrow$ $ xyzw = 711000000$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21844  (x y z w : ℝ)
  (h₀ : 10^(-2:ℤ) * (x + y + z + w) = 7.11)
  (h₁ : (10^(-2:ℤ) * x) * (10^(-2:ℤ) * y) * (10^(-2:ℤ) * z) * (10^(-2:ℤ) * w) = 7.11) :
  x * y * z * w = 711000000   :=  by sorry
