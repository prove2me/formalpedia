-- Prove2me | solution 1 for lean_workbook_plus_24062
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:31.303032+00:00
-- url     : https://prove2.me/submissions/21131029-521d-4815-9c7d-1b1aac1846e6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) : Set.range (fun x : ℝ => x^2 + a) = Set.Ici a := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact show a ≤ x^2+a by nlinarith [sq_nonneg x]
  · intro hy
    refine ⟨Real.sqrt (y-a), ?_⟩
    have hs := Real.sq_sqrt (show 0 ≤ y-a by exact sub_nonneg.mpr hy)
    linarith
