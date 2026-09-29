-- Prove2me | Theorems.Thm_flt5_probe_cyc_both_v1
-- name    : flt5_probe_cyc_both_v1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:45:38.737054+00:00
-- url     : https://prove2.me/theorems/4bb089b4-a202-4952-971e-51a1fea49d08
-- statement:
--   Test all cyclotomic imports

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem flt5_probe_cyc_both_v1 : ∃ ζ : CyclotomicField 5 ℚ, IsPrimitiveRoot ζ 5 ∧ True := by sorry
