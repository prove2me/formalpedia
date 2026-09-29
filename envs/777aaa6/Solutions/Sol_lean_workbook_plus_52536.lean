-- Prove2me | solution 1 for lean_workbook_plus_52536
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:22.978365+00:00
-- url     : https://prove2.me/submissions/e2a74176-69fb-49c9-849b-369d78f4af26

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution :  ∀ a b c : ℝ, a^2 * b^2 * c^2 ≥ |(a^2 - b^2) * (b^2 - c^2) * (c^2 - a^2)| → a^4 * b^4 * c^4 ≥ (a^2 - b^2)^2 * (b^2 - c^2)^2 * (c^2 - a^2)^2 := by
  intro a b c h
  have h' := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ a^2*b^2*c^2 by positivity)).mpr h
  simpa only [sq_abs, mul_pow, ← pow_mul] using h'
