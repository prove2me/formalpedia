-- Prove2me | solution 1 for flt5_probe_open_nf_v1
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:27:26.487644+00:00
-- url     : https://prove2.me/submissions/5daf81c1-3f17-4731-a199-9225e0ab2195

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField in theorem solution (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  exact IsCyclotomicExtension.Rat.five_pid K
#print axioms solution
