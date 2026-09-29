-- Prove2me | Theorems.Thm_flt5_probe_open_nf_v1
-- name    : flt5_probe_open_nf_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T06:05:02.231453+00:00
-- url     : https://prove2.me/theorems/3d9be8e0-e247-48d4-bdda-74b8448d656f
-- statement:
--   Test five_pid with open NumberField

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

open NumberField in theorem flt5_probe_open_nf_v1 (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by sorry
