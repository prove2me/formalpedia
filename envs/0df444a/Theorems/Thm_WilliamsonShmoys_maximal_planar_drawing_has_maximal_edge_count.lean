-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_maximal_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_maximal_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:01:05.519212+00:00
-- url     : https://prove2.me/theorems/c5b13c35-cd7f-4aff-91e6-c51f784ba3dd
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal planar graph on a finite ordered vertex type with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ K.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
