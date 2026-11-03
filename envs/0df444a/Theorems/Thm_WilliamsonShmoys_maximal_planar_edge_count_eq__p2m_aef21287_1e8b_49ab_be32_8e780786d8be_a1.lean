-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq__p2m_aef21287_1e8b_49ab_be32_8e780786d8be_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_aef21287_1e8b_49ab_be32_8e780786d8be_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:55:46.217549+00:00
-- url     : https://prove2.me/theorems/ff906063-5ccb-4e8b-ad72-9b52b363ab18
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A connected simple graph on at least three vertices that has the specified crossing-free drawing and is inclusion-maximal among drawable supergraphs has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_aef21287_1e8b_49ab_be32_8e780786d8be_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M <= L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
