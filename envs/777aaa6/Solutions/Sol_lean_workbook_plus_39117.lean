-- Prove2me | solution 1 for lean_workbook_plus_39117
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:05:14.553829+00:00
-- url     : https://prove2.me/submissions/8b23e57f-54fc-4d89-a8fe-50c63c14c5d3

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  (x * y / (x^2 + (x * y) + y^2) + y * z / (y^2 + (y * z) + z^2) + z * x / (z^2 + (z * x) + x^2)) ≤ 1 := by
  obtain ⟨hx,hy,hz⟩ := h₀
  have bound (a b : ℝ) (ha : 0<a) (hb : 0<b) : a*b/(a^2+a*b+b^2) ≤ 1/3 := by
    have hd : 0<a^2+a*b+b^2 := by positivity
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg (a-b)]
  have hab := bound x y hx hy
  have hbc := bound y z hy hz
  have hca := bound z x hz hx
  linarith
