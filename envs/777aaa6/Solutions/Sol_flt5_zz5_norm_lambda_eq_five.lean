-- Prove2me | solution 1 for flt5_zz5_norm_lambda_eq_five
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T10:41:51.834689+00:00
-- url     : https://prove2.me/submissions/ded88c2e-2277-41c8-914c-0282db828816
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic
import Theorems.Thm_flt5_zz5_norm_lambda_eq_five
import Theorems.Thm_flt5_zz5_norm_lambda_cast

-- Sketch: reduce to the ℚ-cast version then exact_mod_cast.
-- Child: flt5_zz5_norm_lambda_cast proves (norm_ℤ(1-ζ) : ℚ) = 5.

noncomputable section

abbrev ZZ5nlsk := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5nlsk := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5nlsk :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5nlsk :=
  IsCyclotomicExtension.numberField {5} ℚ CK5nlsk

theorem solution (ζ : ZZ5nlsk)
    (hζ : IsPrimitiveRoot (ζ : CK5nlsk) 5) :
    Algebra.norm ℤ (1 - ζ : ZZ5nlsk) = 5 := by
  have h : (Algebra.norm ℤ (1 - ζ : ZZ5nlsk) : ℚ) = 5 :=
    flt5_zz5_norm_lambda_cast ζ hζ
  exact_mod_cast h

end
