-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_planar_edge_lower_bound__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_lower_bound__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:49:49.9923+00:00
-- url     : https://prove2.me/theorems/ff80ea5d-6957-43f8-9fdf-8205a3dcb374
-- title:
--   Maximal drawable graphs meet the planar edge threshold
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has at least $3|V|-6$ edges. The independent proof route is to establish that maximality forces a connected triangulation, and then use Euler's formula and face-edge incidence counting. This is the main remaining topological obligation; the inequality's direction and the three-vertex boundary case agree with the standard planar bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_lower_bound__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (hL : HasPlanarDrawingOn L)
    (hLmax : ∀ M : SimpleGraph V, L < M → ¬ HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ L.edgeFinset.card := by sorry
