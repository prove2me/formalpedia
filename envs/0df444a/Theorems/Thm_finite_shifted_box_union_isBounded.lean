-- Prove2me | Theorems.Thm_finite_shifted_box_union_isBounded
-- name    : finite_shifted_box_union_isBounded
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:11:33.100951+00:00
-- url     : https://prove2.me/theorems/c958de9e-0b64-40bb-8d41-f7d345e7a9c9
-- title:
--   A finite union of shifted unit boxes is bounded
-- statement:
--   For any finite index set and any family of natural-number shifts in a finite-dimensional real function space, the union of the corresponding coordinatewise unit boxes is bounded. Prove each box is bounded by coordinate estimates and combine the bounds using Mathlib’s finite bounded-union theorem. This also covers an empty index set and dimension zero.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem finite_shifted_box_union_isBounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Nat) (s : Finset ι) (a : ι → Fin n → Nat) :
    Bornology.IsBounded
      (⋃ j ∈ (s : Set ι),
        {x : Fin n → Real | ∀ i, (a j i : Real) ≤ x i ∧ x i < (a j i : Real) + 1}) := by sorry
