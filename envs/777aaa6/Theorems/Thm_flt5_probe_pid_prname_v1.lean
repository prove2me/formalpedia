-- Prove2me | Theorems.Thm_flt5_probe_pid_prname_v1
-- name    : flt5_probe_pid_prname_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:49:11.337657+00:00
-- url     : https://prove2.me/theorems/4009c7a4-6f6e-4dea-823d-7a1371794ac3
-- statement:
--   probe A

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.PID

theorem flt5_probe_pid_prname_v1 (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by sorry
