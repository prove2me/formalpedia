-- Prove2me | Theorems.Thm_furstenberg_x2_x3_conjecture
-- name    : furstenberg_x2_x3_conjecture
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-31T20:39:05.909458+00:00
-- url     : https://prove2.me/theorems/d32d5825-f5d2-4152-aaec-b61d1900fabf
-- statement:
--   Furstenberg's ×2 ×3 conjecture (1967): The only Borel probability measure on ℝ/ℤ simultaneously invariant under x↦2x and x↦3x is the Lebesgue measure. Partial results by Rudolph (1990) and Host (1995); full conjecture open.
-- source:
--   https://en.wikipedia.org/wiki/Furstenberg_conjecture

import Mathlib

import Mathlib

theorem furstenberg_x2_x3_conjecture
    (mu2 : MeasureTheory.Measure (AddCircle (1 : ℝ)))
    (hprob : mu2 Set.univ = 1)
    (h2inv : ∀ S : Set (AddCircle (1 : ℝ)), MeasurableSet S →
      mu2 S = mu2 (Set.preimage (fun x => (2 : ℤ) • x) S))
    (h3inv : ∀ S : Set (AddCircle (1 : ℝ)), MeasurableSet S →
      mu2 S = mu2 (Set.preimage (fun x => (3 : ℤ) • x) S)) :
    mu2 = MeasureTheory.volume := by
  sorry
