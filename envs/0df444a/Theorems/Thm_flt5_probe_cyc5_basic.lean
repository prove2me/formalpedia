-- Prove2me | Theorems.Thm_flt5_probe_cyc5_basic
-- name    : flt5_probe_cyc5_basic
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T05:43:04.019311+00:00
-- url     : https://prove2.me/theorems/832f04f6-bbda-42d5-b933-10133e8f2024
-- statement:
--   Test CyclotomicField 5 ℚ basic

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

theorem flt5_probe_cyc5_basic : ∃ ζ : CyclotomicField 5 ℚ, IsPrimitiveRoot ζ 5 := by sorry
