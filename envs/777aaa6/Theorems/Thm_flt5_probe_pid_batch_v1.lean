-- Prove2me | Theorems.Thm_flt5_probe_pid_batch_v1
-- name    : flt5_probe_pid_batch_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:59:37.992597+00:00
-- url     : https://prove2.me/theorems/8152c359-02f2-4ea9-8d2d-de12e3305fc9
-- statement:
--   batch probe

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.PID

theorem flt5_probe_pid_batch_v1 (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by sorry
