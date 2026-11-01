-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_can_be_strictly_augmented_when_below_bound__p2m_300e589a_9958_4177_9a18_5a010b7286b4_a1
-- name    : WilliamsonShmoys.planar_drawing_can_be_strictly_augmented_when_below_bound__p2m_300e589a_9958_4177_9a18_5a010b7286b4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:40.653372+00:00
-- url     : https://prove2.me/theorems/17cdf377-ddf7-4ef9-90d4-89407a0a5949
-- title:
--   A drawable graph below the planar bound has a drawable proper extension
-- statement:
--   For a finite drawable simple graph on at least three vertices, if its edge count is below 3|V|−6, it has a drawable proper supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_can_be_strictly_augmented_when_below_bound__p2m_300e589a_9958_4177_9a18_5a010b7286b4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := dK;
      K.edgeFinset.card < 3 * Fintype.card V - 6) →
      ∃ M : SimpleGraph V, K ≤ M ∧ ¬ M ≤ K ∧ HasPlanarDrawingOn M := by sorry
