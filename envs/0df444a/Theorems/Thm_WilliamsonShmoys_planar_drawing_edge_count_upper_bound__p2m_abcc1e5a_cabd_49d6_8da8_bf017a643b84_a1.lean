-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:29:08.306636+00:00
-- url     : https://prove2.me/theorems/acd844a2-f18b-4cf8-8cd2-2591d79fbd14
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every simple graph with a drawing satisfying the supplied crossing-free arc predicate and at least three vertices has at most 3|V|−6 edges. The boundary case |V|=3 allows at most all three possible edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
