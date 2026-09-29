-- Prove2me | solution 1 for lean_workbook_plus_25564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:26.516368+00:00
-- url     : https://prove2.me/submissions/4f7b9b3a-2fa3-4895-9d12-49370864528b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c : ℝ)
  (h₀ : a = 1 / 100)
  (h₁ : b = 99 / 100)
  (h₂ : c = 5) :
  (a + 1 / a) * (b + 1 / b) * (c + 1 / c) > 1000 := by
  subst a
  subst b
  subst c
  norm_num
