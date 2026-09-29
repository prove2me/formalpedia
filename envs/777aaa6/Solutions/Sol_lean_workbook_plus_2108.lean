-- Prove2me | solution 1 for lean_workbook_plus_2108
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:10.889875+00:00
-- url     : https://prove2.me/submissions/845fab39-546f-4cdf-9434-d2e293176d42

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ {x y z t : ℝ}, x + y = y + z ∧ y + z = z + t ∧ z + t = t + x ↔ x = z ∧ y = t := by
  intro x y z t
  constructor
  · rintro ⟨h1,h2,h3⟩
    constructor <;> linarith
  · rintro ⟨rfl,rfl⟩
    constructor
    · ring
    constructor <;> ring
