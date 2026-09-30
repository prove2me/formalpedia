-- Prove2me | solution 1 for flt5_probe_adjoin_pid_v1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:56:24.76221+00:00
-- url     : https://prove2.me/submissions/08b87fdb-57ce-4907-9f5b-de7275e8dad9

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic

open NumberField

theorem solution : IsPrincipalIdealRing (𝓞 (CyclotomicField 5 ℚ)) := by
  letI : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  exact IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)

#check @solution
#print axioms solution
