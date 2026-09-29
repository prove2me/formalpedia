-- Prove2me | Theorems.Thm_flt5_zz5_norm_galois_prod
-- name    : flt5_zz5_norm_galois_prod
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T14:37:51.118658+00:00
-- url     : https://prove2.me/theorems/6d705b7e-890e-480a-b3a3-6bcdde67fcee
-- statement:
--   Galois norm product formula for CyclotomicField 5 Q: For a,b:Z and zeta a primitive 5th root of unity, algebraMap Q CK5 (Algebra.norm Q (a+zeta*b)) = (a+zeta*b)*(a+zeta^2*b)*(a+zeta^3*b)*(a+zeta^4*b). This follows from IsGalois.norm_eq_prod_automorphisms applied to CK5/Q (which is Galois with group Z/4Z), where the 4 automorphisms send zeta to zeta^k for k=1,2,3,4.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic

theorem flt5_zz5_norm_galois_prod (a b : ℤ) (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : algebraMap ℚ (CyclotomicField 5 ℚ) (Algebra.norm ℚ ((a : CyclotomicField 5 ℚ) + ζ * b)) = ((a : CyclotomicField 5 ℚ) + ζ * b) * (a + ζ ^ 2 * b) * (a + ζ ^ 3 * b) * (a + ζ ^ 4 * b) := by sorry
