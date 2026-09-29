-- Prove2me | Theorems.Thm_flt5_probe_pid_all_v1
-- name    : flt5_probe_pid_all_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:45:56.340202+00:00
-- url     : https://prove2.me/theorems/c8bbec30-c9da-482d-9904-286dd200af54
-- statement:
--   Test PID for adjoin of primitive root

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.PID

theorem flt5_probe_pid_all_v1 (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by sorry
