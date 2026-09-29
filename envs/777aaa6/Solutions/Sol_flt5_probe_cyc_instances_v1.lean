-- Prove2me | solution 1 for flt5_probe_cyc_instances_v1
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:27:25.784936+00:00
-- url     : https://prove2.me/submissions/c427731e-0af0-4a7d-9dae-00ce614a9949

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField in theorem solution : IsPrincipalIdealRing (𝓞 (CyclotomicField 5 ℚ)) := by
  letI : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) := CyclotomicField.isCyclotomicExtension 5 ℚ
  exact IsCyclotomicExtension.Rat.five_pid (CyclotomicField 5 ℚ)
#print axioms solution
