-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_of_maximality
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_of_maximality
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:31:54.45917+00:00
-- url     : https://prove2.me/theorems/9bdaaf9b-5dc9-45cd-bdd3-be1c3702e1ee
-- title:
--   Maximal drawn planar graphs have the triangular edge count
-- statement:
--   A drawn graph on at least three vertices that has no strict drawn supergraph on those vertices has exactly $3|V|-6$ edges. The independent proof route is to formalize that maximality forces a triangulation, then use Euler's formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_of_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
