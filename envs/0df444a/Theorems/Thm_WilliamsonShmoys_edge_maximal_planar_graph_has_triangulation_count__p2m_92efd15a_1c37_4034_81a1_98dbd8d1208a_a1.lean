-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_triangulation_count__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_has_triangulation_count__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:28.50399+00:00
-- url     : https://prove2.me/theorems/c4417236-d2c3-4bc2-b2ac-88bc17b75d38
-- title:
--   Edge-maximal planar graphs have the triangulation edge count
-- statement:
--   For at least three vertices, an edge-inclusion-maximal graph with the given planar drawing has exactly 3|V|−6 edges. The proof uses maximality to establish triangular faces and then applies Euler's formula for planar embeddings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_graph_has_triangulation_count__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
