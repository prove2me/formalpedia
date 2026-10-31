-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:11.219776+00:00
-- url     : https://prove2.me/theorems/e0e04b13-f360-445e-bd9a-b3847171c53c
-- title:
--   Maximality forces the triangulation edge count
-- statement:
--   A finite simple graph with at least three vertices that is maximal among graphs admitting the supplied planar drawing has at least 3|V|−6 edges. The standard route augments a planar graph to a triangulation and uses maximality to show the augmentation adds no edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by sorry
