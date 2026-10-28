-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:03:47.451341+00:00
-- url     : https://prove2.me/theorems/820a3c18-eada-476d-b397-fdb3bfba4e4e
-- title:
--   Maximal drawable graphs meet the planar edge lower bound
-- statement:
--   For at least three vertices, an inclusion-maximal simple graph admitting the specified crossing-free drawing has at least 3|V| − 6 edges. A proof route is to establish connectedness and triangular faces from maximality, then apply Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) :
    3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by sorry
