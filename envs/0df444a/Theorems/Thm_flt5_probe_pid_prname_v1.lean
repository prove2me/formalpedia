-- Prove2me | Theorems.Thm_flt5_probe_pid_prname_v1
-- name    : flt5_probe_pid_prname_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:49:11.337657+00:00
-- url     : https://prove2.me/theorems/3297923e-4012-4410-b8ea-d0c15763197d
-- statement:
--   probe A

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem flt5_probe_pid_prname_v1 (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by sorry
