-- Prove2me | Theorems.Thm_flt5_probe_int_closure_v1
-- name    : flt5_probe_int_closure_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T06:05:53.060688+00:00
-- url     : https://prove2.me/theorems/cf0f4762-43fd-4682-aa56-6d03ea0379da
-- statement:
--   Test isIntegralClosure for adjoin

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

open NumberField in theorem flt5_probe_int_closure_v1 (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) : IsIntegralClosure (Algebra.adjoin ℤ ({ζ} : Set K)) ℤ K := by sorry
