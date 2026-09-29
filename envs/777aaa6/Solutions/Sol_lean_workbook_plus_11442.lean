-- Prove2me | solution 1 for lean_workbook_plus_11442
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:25.593881+00:00
-- url     : https://prove2.me/submissions/14b94b9b-6d9a-4f18-8a5e-a391d5c5db01

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℚ) : ∃ a b : ℤ, b > 0 ∧ x = a / b := by
  refine ⟨x.num,x.den,by exact_mod_cast x.pos,?_⟩
  simpa using (Rat.num_div_den x).symm
