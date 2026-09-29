-- Prove2me | Theorems.Thm_flt5_probe_algmap_v1
-- name    : flt5_probe_algmap_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T06:31:12.687438+00:00
-- url     : https://prove2.me/theorems/170342d4-eab2-47d4-ad93-637468adbfd4
-- statement:
--   Test algebraMap into ring of integers

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem flt5_probe_algmap_v1 (a : ℤ) : ∃ x : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), (x : CyclotomicField 5 ℚ) = algebraMap ℤ (CyclotomicField 5 ℚ) a := by sorry
