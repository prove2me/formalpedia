-- Prove2me | Theorems.Thm_flt5_probe_pid_cycle_rat_v1
-- name    : flt5_probe_pid_cycle_rat_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:49:34.766231+00:00
-- url     : https://prove2.me/theorems/effd08d8-6389-47a9-9897-8ed21e722438
-- statement:
--   probe B

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem flt5_probe_pid_cycle_rat_v1 (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by sorry
