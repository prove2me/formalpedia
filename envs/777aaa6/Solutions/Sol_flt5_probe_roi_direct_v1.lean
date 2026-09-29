-- Prove2me | solution 1 for flt5_probe_roi_direct_v1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-13T06:20:11.885896+00:00
-- url     : https://prove2.me/submissions/dc55a05b-20d0-43ec-ac48-6bcd350f05a9

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

theorem solution : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) := by
  haveI h1 : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) := 
    CyclotomicField.isCyclotomicExtension 5 ℚ
  haveI h2 : NumberField (CyclotomicField 5 ℚ) := 
    IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)
  exact IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)
