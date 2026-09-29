-- Prove2me | Theorems.Thm_flt5_probe_cyc_instances_v1
-- name    : flt5_probe_cyc_instances_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T06:18:47.244807+00:00
-- url     : https://prove2.me/theorems/658e3e95-a0c7-47ec-a061-7b56917fafa0
-- statement:
--   Test with all three cyclotomic imports

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

open NumberField in theorem flt5_probe_cyc_instances_v1 : IsPrincipalIdealRing (𝓞 (CyclotomicField 5 ℚ)) := by sorry
