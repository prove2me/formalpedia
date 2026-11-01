-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:35.861741+00:00
-- url     : https://prove2.me/theorems/977e0484-c39c-4e95-a5d4-5a834f8539e1
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    letI : DecidableRel M.Adj := Classical.decRel M.Adj
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
