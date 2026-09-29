-- Prove2me | solution 1 for lean_workbook_plus_33014
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:40:38.556731+00:00
-- url     : https://prove2.me/submissions/8016a98a-111a-483e-8674-ce294e9b1682

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : Real.sqrt (Real.sqrt n + n + 2) < Real.sqrt (n + 1) + 1 := by
  have hn : (0:ℝ) ≤ n := by positivity
  have hs := Real.sqrt_nonneg (n:ℝ)
  have ht := Real.sqrt_nonneg ((n:ℝ)+1)
  have hlt : Real.sqrt (n:ℝ) < Real.sqrt ((n:ℝ)+1) :=
    Real.sqrt_lt_sqrt hn (by linarith)
  have ht2 := Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
  apply (Real.sqrt_lt' (show 0 < Real.sqrt ((n:ℝ)+1)+1 by positivity)).mpr
  nlinarith only [hs, ht, hlt, ht2]
