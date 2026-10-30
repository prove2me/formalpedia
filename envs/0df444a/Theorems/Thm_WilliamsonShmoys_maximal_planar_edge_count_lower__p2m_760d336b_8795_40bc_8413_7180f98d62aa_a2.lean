-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:22.21976+00:00
-- url     : https://prove2.me/theorems/e0d9ce97-e019-42af-a0bd-4118a7b4d4c1
-- title:
--   Maximal planarity forces the matching edge lower bound
-- statement:
--   A connected graph maximal among planar supergraphs on the same finite vertex set, with at least three vertices, has at least 3|V|−6 edges. The proof route is to use maximality to force a triangulation and then apply Euler's formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      (letI : DecidableRel L.Adj := dL
       H <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= H))
    (hcard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= H.edgeFinset.card := by sorry
