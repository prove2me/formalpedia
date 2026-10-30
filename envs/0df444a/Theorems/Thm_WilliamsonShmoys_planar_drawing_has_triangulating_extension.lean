-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulating_extension
-- name    : WilliamsonShmoys.planar_drawing_has_triangulating_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:49:01.117549+00:00
-- url     : https://prove2.me/theorems/8070196b-3326-411c-a9ac-119c796c6d1d
-- title:
--   Extend a finite planar drawing to a maximal planar graph
-- statement:
--   For every drawable simple graph on at least three vertices, there is a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6, and the original edge count is no larger. The inclusion and count inequality make the final reduction independent of any particular finite-set cardinality API.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulating_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T.edgeSet ⊆ U.edgeSet ∧
      HasPlanarDrawingOn U ∧
      T.edgeSet.ncard ≤ U.edgeSet.ncard ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
