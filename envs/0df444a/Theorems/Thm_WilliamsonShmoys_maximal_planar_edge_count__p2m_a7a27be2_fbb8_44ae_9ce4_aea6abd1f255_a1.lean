-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a7a27be2_fbb8_44ae_9ce4_aea6abd1f255_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_a7a27be2_fbb8_44ae_9ce4_aea6abd1f255_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:06.263195+00:00
-- url     : https://prove2.me/theorems/42afe04b-4ecc-4d48-9c38-07e79025e31e
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   A simple graph on at least three vertices that has a crossing-free drawing and is maximal among drawable supergraphs on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_a7a27be2_fbb8_44ae_9ce4_aea6abd1f255_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
