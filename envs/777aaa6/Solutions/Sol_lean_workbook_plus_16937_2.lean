-- Prove2me | solution 2 for lean_workbook_plus_16937
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:10.893727+00:00
-- url     : https://prove2.me/submissions/41e66d80-5e6c-436f-aad6-9774aa656e9e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution :
  IsGreatest {y : ℝ | ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ y = 2 * x * (1 - x)^2} (8 / 27) := by
  constructor
  · exact ⟨1/3,by norm_num,by norm_num,by norm_num⟩
  · rintro y ⟨x,hx0,hx1,rfl⟩
    nlinarith [mul_nonneg (sq_nonneg (x-1/3)) (show 0 ≤ 4/3-x by linarith)]
