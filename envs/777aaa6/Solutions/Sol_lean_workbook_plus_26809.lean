-- Prove2me | solution 1 for lean_workbook_plus_26809
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:05.259088+00:00
-- url     : https://prove2.me/submissions/b668b004-f39b-4967-8845-0f45bd510310

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℤ, 4 ∣ 2 * n * (n + 1) := by
  intro n
  rcases Int.two_dvd_mul_add_one n with ⟨k,hk⟩
  refine ⟨k,?_⟩
  nlinarith
