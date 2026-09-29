-- Prove2me | solution 1 for TwoTreeClosure.gaussSum_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:41:30.544064+00:00
-- url     : https://prove2.me/submissions/9e4e12d7-16f4-4031-8aa8-da5693ef969c

import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_GaussDial
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
open TwoTreeClosure in
theorem solution (M N k : ℕ) (hM : 0 < M) :
    gaussSum M (N + k * M) = gaussSum M N := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold TwoTreeClosure.gaussSum
  refine Finset.sum_congr rfl fun x _ => ?_
  -- the extra `k M` in the numerator contributes `x² k` full turns
  calc Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) ^ 2 * ((N + k * M : ℕ) : ℂ)) / (M : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) ^ 2 * (N : ℂ)) / (M : ℂ)
          + ((x ^ 2 * k : ℕ) : ℂ) * (2 * Real.pi * Complex.I)) := by
        congr 1
        push_cast
        field_simp
    _ = Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) ^ 2 * (N : ℂ)) / (M : ℂ)) := by
        rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
