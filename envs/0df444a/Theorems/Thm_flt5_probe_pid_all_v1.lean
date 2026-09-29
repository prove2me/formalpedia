-- Prove2me | Theorems.Thm_flt5_probe_pid_all_v1
-- name    : flt5_probe_pid_all_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:45:56.340202+00:00
-- url     : https://prove2.me/theorems/cbbde064-78e7-4a46-b467-9b558314057c
-- statement:
--   Test PID for adjoin of primitive root

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem flt5_probe_pid_all_v1 (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by sorry
