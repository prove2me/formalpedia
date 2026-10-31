-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_3a65eae3_5ff7_4fce_93d5_4a7db05ee858_a1
-- name    : WilliamsonShmoys_maximal_planar_edge_count__p2m_3a65eae3_5ff7_4fce_93d5_4a7db05ee858_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:56:12.085553+00:00
-- url     : https://prove2.me/theorems/2508ece6-24ff-4a9a-9901-7572a4f15f41
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite connected simple graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has exactly 3|V|−6 edges. This is the topological core: maximality forces a triangulation, whose planar edge count gives the equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_edge_count__p2m_3a65eae3_5ff7_4fce_93d5_4a7db05ee858_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
