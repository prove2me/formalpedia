-- Prove2me | Theorems.Thm_bounded_set_volume_ne_top
-- name    : bounded_set_volume_ne_top
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:01:56.982224+00:00
-- url     : https://prove2.me/theorems/fd0aaff6-3aaf-483d-b492-6becc2119cc5
-- title:
--   Bounded subsets of finite-dimensional real space have finite volume
-- statement:
--   Every bounded subset of finite-dimensional real space has finite Lebesgue volume, without requiring measurability. Bound it by a bounded box, whose volume is finite, and apply monotonicity.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem bounded_set_volume_ne_top
    {n : Nat} (s : Set (Fin n → Real)) (hs : Bornology.IsBounded s) :
    MeasureTheory.volume s ≠ ⊤ := by sorry
