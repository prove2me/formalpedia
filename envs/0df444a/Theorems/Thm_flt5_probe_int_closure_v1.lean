-- Prove2me | Theorems.Thm_flt5_probe_int_closure_v1
-- name    : flt5_probe_int_closure_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T06:05:53.060688+00:00
-- url     : https://prove2.me/theorems/f6f979f5-6270-494b-9589-5ba6a3bca714
-- statement:
--   Test isIntegralClosure for adjoin

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

open NumberField in theorem flt5_probe_int_closure_v1 (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) : IsIntegralClosure (Algebra.adjoin ℤ ({ζ} : Set K)) ℤ K := by sorry
