-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exact_edge_count__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exact_edge_count__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:28:59.461441+00:00
-- url     : https://prove2.me/theorems/c7a07234-8856-4e73-ae2f-62c3fa66bc64
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that maximizes edge count among its drawable supergraphs on the same vertex set has exactly 3|V|−6 edges. This isolates the planar topology and counting argument from finite maximization. A proof route is to represent the given drawing as a plane embedding, use maximality to show that every face is triangular, then apply Euler’s formula and count incidences between faces and edges. The vertex-count hypothesis is essential for the stated formula and includes the three-vertex case, where maximality yields the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exact_edge_count__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
