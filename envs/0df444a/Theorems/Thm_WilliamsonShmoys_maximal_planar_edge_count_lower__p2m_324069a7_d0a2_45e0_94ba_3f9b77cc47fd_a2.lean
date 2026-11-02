-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:39:01.775873+00:00
-- url     : https://prove2.me/theorems/aef21287-1e8b-49ab-be32-8e780786d8be
-- title:
--   Maximal planar graph edge-count lower bound
-- statement:
--   A connected graph on at least three vertices with the specified drawing that is inclusion-maximal among drawable supergraphs has at least three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M <= L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by sorry
