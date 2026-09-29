-- Prove2me | Theorems.Thm_flt5_probe_pid_C
-- name    : flt5_probe_pid_C
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:50:57.56322+00:00
-- url     : https://prove2.me/theorems/8d8949cb-86e8-4b05-ba02-e8c02213c653
-- statement:
--   probe C

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem flt5_probe_pid_C (ζ : CyclotomicField 5 ℚ) (hζ : IsPrimitiveRoot ζ 5) : IsPrincipalIdealRing (Algebra.adjoin ℤ ({ζ} : Set (CyclotomicField 5 ℚ))) := by sorry
