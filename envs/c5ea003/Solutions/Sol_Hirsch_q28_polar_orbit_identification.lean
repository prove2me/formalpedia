-- Prove2me | solution 1 for Hirsch.q28_polar_orbit_identification
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-06T00:20:40.795534+00:00
-- url     : https://prove2.me/submissions/b6c2e189-e9a1-478b-9d06-d8b213b369b7

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert
import Theorems.Thm_Hirsch_q28_extreme_classification
import Theorems.Thm_Hirsch_q28_adj_to_orbit

open scoped RealInnerProductSpace
open Set Hirsch

theorem solution :
    (∀ x : EuclideanSpace ℝ (Fin 5),
      x ∈ extremePoints ℝ (Hpoly q28A q28B) →
        ∃ o : Fin 20, ∃ s : Fin 16, x = flipPoint s (orbitPoint o)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin 5),
      Adj (Hpoly q28A q28B) x y →
        ∃ o1 o2 : Fin 20, ∃ s1 s2 : Fin 16,
          x = flipPoint s1 (orbitPoint o1) ∧
          y = flipPoint s2 (orbitPoint o2) ∧
          (o1 = o2 ∨ QuotientAdj o1 o2)) ∧
    (∀ x : EuclideanSpace ℝ (Fin 5), ∀ o1 o2 : Fin 20, ∀ s1 s2 : Fin 16,
      x = flipPoint s1 (orbitPoint o1) →
      x = flipPoint s2 (orbitPoint o2) → o1 = o2) ∧
    q28U = flipPoint 0 (orbitPoint 1) ∧
    q28V = flipPoint 0 (orbitPoint 0) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 1) = q28U) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 0) = q28V) := by
  obtain ⟨hextr, huniq, hU, hV, hUf, hVf⟩ := q28_extreme_classification
  exact ⟨hextr, q28_adj_to_orbit, huniq, hU, hV, hUf, hVf⟩
