-- Prove2me | solution 1 for flt5_probe_pid_C
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T02:42:21.812559+00:00
-- url     : https://prove2.me/submissions/cf34fcf1-aba2-47e3-8523-481be52687e0

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

theorem solution (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) :
    IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by
  haveI : IsCyclotomicExtension ({5} : Set ℕ) ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  haveI : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) :=
    IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)
  let e := hζ.adjoinEquivRingOfIntegers (K := CyclotomicField 5 ℚ)
  exact IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
