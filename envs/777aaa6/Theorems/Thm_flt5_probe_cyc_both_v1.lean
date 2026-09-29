-- Prove2me | Theorems.Thm_flt5_probe_cyc_both_v1
-- name    : flt5_probe_cyc_both_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:45:38.737054+00:00
-- url     : https://prove2.me/theorems/00a61b54-e6d1-4d1a-a02e-faf2a16a39dd
-- statement:
--   Test all cyclotomic imports

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.PID

theorem flt5_probe_cyc_both_v1 : ∃ ζ : CyclotomicField 5 ℚ, IsPrimitiveRoot ζ 5 ∧ True := by sorry
