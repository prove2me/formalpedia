-- Prove2me | Theorems.Thm_shifted_boxes_isBounded
-- name    : shifted_boxes_isBounded
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:01:34.487372+00:00
-- url     : https://prove2.me/theorems/9030d1d6-7a82-4e9e-8f1b-66bb563c4fff
-- title:
--   The finite union of shifted unit boxes is bounded
-- statement:
--   For positive weights and positive T, the union of boxes indexed by the strict weighted simplex is bounded. The index set is finite by the supplied definition; each box is bounded coordinatewise, and finite unions of bounded sets are bounded. For n = 0 the product is the singleton empty function, so the same conclusion holds.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem shifted_boxes_isBounded
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    Bornology.IsBounded
      (⋃ a ∈ (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)),
        {x : Fin n → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) := by sorry
