-- Prove2me | solution 1 for flt5_probe_algmap_v1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T02:34:34.118167+00:00
-- url     : https://prove2.me/submissions/ad6c798f-a85f-4bda-af0a-1bf2922be965

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic

theorem solution (a : ℤ) :
    ∃ x : NumberField.RingOfIntegers (CyclotomicField 5 ℚ),
    (x : CyclotomicField 5 ℚ) = algebraMap ℤ (CyclotomicField 5 ℚ) a :=
  ⟨⟨algebraMap ℤ (CyclotomicField 5 ℚ) a, isIntegral_algebraMap⟩, rfl⟩
