-- Prove2me | solution 1 for lean_workbook_plus_6511
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:21:30.269556+00:00
-- url     : https://prove2.me/submissions/27106282-ee7d-49dc-9ef5-96d9cbd349dc

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (hp : p.Prime) (h : (-5 : ZMod p) = 1 ∨ (-5 : ZMod p) = 2) : ∃ a b : ℤ, (a^2 + 5 * b^2) % p = 1 ∨ (a^2 + 5 * b^2) % p = 2 := by
  refine ⟨1, 0, Or.inl ?_⟩
  have h2 : 2 ≤ p := hp.two_le
  norm_num
  exact Int.emod_eq_of_lt (by norm_num) (by omega)
