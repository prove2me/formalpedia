-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:46:00.796909+00:00
-- url     : https://prove2.me/theorems/d9ec561c-5413-404b-9cc9-bfd18ae2ee8f
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A connected graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex type has at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by sorry
