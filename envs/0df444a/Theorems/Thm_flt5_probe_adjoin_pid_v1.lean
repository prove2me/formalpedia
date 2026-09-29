-- Prove2me | Theorems.Thm_flt5_probe_adjoin_pid_v1
-- name    : flt5_probe_adjoin_pid_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T06:12:40.312656+00:00
-- url     : https://prove2.me/theorems/8fb684f2-5dbf-45c2-b217-b8cc9cdfaca3
-- statement:
--   Test IsPrincipalIdealRing for ring of integers of CyclotomicField 5 ℚ

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic

open NumberField in theorem flt5_probe_adjoin_pid_v1 : IsPrincipalIdealRing (𝓞 (CyclotomicField 5 ℚ)) := by sorry
