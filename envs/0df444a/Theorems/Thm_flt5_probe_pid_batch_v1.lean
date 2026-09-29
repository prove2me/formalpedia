-- Prove2me | Theorems.Thm_flt5_probe_pid_batch_v1
-- name    : flt5_probe_pid_batch_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:59:37.992597+00:00
-- url     : https://prove2.me/theorems/0b718b80-5c24-4c45-881a-415e89586050
-- statement:
--   batch probe

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem flt5_probe_pid_batch_v1 (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by sorry
