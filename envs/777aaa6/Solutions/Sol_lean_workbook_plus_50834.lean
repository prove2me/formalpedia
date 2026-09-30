-- Prove2me | solution 1 for lean_workbook_plus_50834
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:10:04.149022+00:00
-- url     : https://prove2.me/submissions/027bc4a7-af3c-4984-b454-5c850869d118

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (n : ℤ) :
    n ^ 2 + 1 ∣ (n ^ 2 + 2) ^ 2 + (n ^ 2 + n + 1) ^ 2 := by
  refine ⟨2 * n ^ 2 + 2 * n + 5, ?_⟩
  ring

#print axioms solution
