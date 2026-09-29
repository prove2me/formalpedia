-- Prove2me | solution 1 for lean_workbook_plus_77640
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:56.029335+00:00
-- url     : https://prove2.me/submissions/84ec2d21-71d8-4660-8996-5592943f7664

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (A : Type*) [Finite A] (f : A → A) (hf: Function.Surjective f) : Function.Injective f := by
  exact Finite.injective_iff_surjective.mpr hf
