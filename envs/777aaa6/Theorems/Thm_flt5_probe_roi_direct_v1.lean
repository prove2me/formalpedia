-- Prove2me | Theorems.Thm_flt5_probe_roi_direct_v1
-- name    : flt5_probe_roi_direct_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T06:19:57.007099+00:00
-- url     : https://prove2.me/theorems/3be6d829-65c2-43a6-9c7e-e2fcf7d5e851
-- statement:
--   Test IsPrincipalIdealRing with fully qualified RingOfIntegers

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

theorem flt5_probe_roi_direct_v1 : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) := by sorry
