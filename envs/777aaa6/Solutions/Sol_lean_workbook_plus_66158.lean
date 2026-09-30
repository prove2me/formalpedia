-- Prove2me | solution 1 for lean_workbook_plus_66158
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:18:10.414443+00:00
-- url     : https://prove2.me/submissions/6c62e43e-c714-45e5-a902-47891efa5493

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hxy : x ≥ y) : x^n ≥ y^n   := by
  induction' n with pn hpn
  simp only [pow_zero, le_refl]
  have h1 : 0 ≤ x ∧ 0 ≤ y := ⟨hx.1.le, hy.1.le⟩
  have h2 : 0 ≤ x^pn ∧ 0 ≤ y^pn := ⟨pow_nonneg h1.1 pn, pow_nonneg h1.2 pn⟩
  rw [pow_succ, pow_succ]
  nlinarith [hpn, hxy]

#print axioms solution
