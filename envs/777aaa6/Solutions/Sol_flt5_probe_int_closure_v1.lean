-- Prove2me | solution 1 for flt5_probe_int_closure_v1
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:21:06.682856+00:00
-- url     : https://prove2.me/submissions/b2946671-fd3a-4c86-9797-fec782acd267

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
set_option autoImplicit false

open NumberField in theorem solution (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) : IsIntegralClosure (Algebra.adjoin ℤ ({ζ} : Set K)) ℤ K := by
  exact IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ
#print axioms solution
