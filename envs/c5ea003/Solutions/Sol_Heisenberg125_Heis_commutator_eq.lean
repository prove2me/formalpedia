-- Prove2me | solution 1 for Heisenberg125.Heis.commutator_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:36:22.849676+00:00
-- url     : https://prove2.me/submissions/4c12df41-942a-4525-8011-3bcf0816b9f5

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic

open Heisenberg125 Heis

variable {p : ℕ}

theorem solution (g h : Heis p) :
    g * h * g⁻¹ * h⁻¹ = ⟨0, 0, g.a * h.b - h.a * g.b⟩ := by
  ext <;> simp [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c] <;> ring
