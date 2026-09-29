-- Prove2me | Theorems.Thm_lean_workbook_plus_52585
-- name    : lean_workbook_plus_52585
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/33d4ecbd-05e5-4a7e-a181-def4d1e3119b
-- statement:
--   If we calling this value a, AD as m, and BD as n, we now have $ n^2+a^2=25$ and $ m^2+a^2=9$ . Subtracting yields $ n^2-m^2=16$ . This factors to $ (n-m)(n+m)=16$ , and we know that $ m+n=7$ . Therefore, $ n-m=\dfrac{16}{7}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52585  (a m n : ℝ)
  (h₀ : n^2 + a^2 = 25)
  (h₁ : m^2 + a^2 = 9)
  (h₂ : m + n = 7) :
  n - m = 16 / 7   :=  by sorry
