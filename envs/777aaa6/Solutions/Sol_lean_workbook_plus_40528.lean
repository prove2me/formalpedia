-- Prove2me | solution 1 for lean_workbook_plus_40528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:33.057763+00:00
-- url     : https://prove2.me/submissions/d4551a4f-e2d5-499e-8b17-145c368e2a73

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ {a x y : ℤ} (h₁ : a ∣ x) (h₂ : a ∣ y), a ∣ x + y ∧ a ∣ x - y ∧ ∀ p q : ℤ, a ∣ p * x + q * y := by
  intro a x y hx hy
  refine ⟨dvd_add hx hy,dvd_sub hx hy,?_⟩
  intro p q
  exact dvd_add (dvd_mul_of_dvd_right hx p) (dvd_mul_of_dvd_right hy q)
