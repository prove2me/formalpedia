-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_simple_graph_edge_bound__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
-- name    : WilliamsonShmoys.maximal_drawable_simple_graph_edge_bound__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:38.031281+00:00
-- url     : https://prove2.me/theorems/6bdbdb3d-755f-4cae-8333-ac9716c72254
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable finite simple graph with at least three vertices has at most 3|V| − 6 edges. The proof route is to establish that maximality forces a connected triangulated embedding, count incidences to obtain 3f = 2m, and combine this with Euler’s formula n − m + f = 2. The condition |V| ≥ 3 covers the smallest triangulated case; the exact drawing predicate supplies the noncrossing embedding needed for the topological argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_simple_graph_edge_bound__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel _
     K.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  sorry
