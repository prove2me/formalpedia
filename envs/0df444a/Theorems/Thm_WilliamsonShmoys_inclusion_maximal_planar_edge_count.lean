-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_edge_count
-- name    : WilliamsonShmoys.inclusion_maximal_planar_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:40:25.661906+00:00
-- url     : https://prove2.me/theorems/17ae40c4-7df7-402a-a395-f9cc6fd50d44
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   A planar graph on at least three vertices that is maximal under edge inclusion among planar graphs on the same vertices has exactly 3|V|−6 edges. The proof uses maximality to establish a triangulated planar embedding and Euler’s formula; the lower bound includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.inclusion_maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      Set.Subset H.edgeSet K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      Set.Subset K.edgeSet H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
