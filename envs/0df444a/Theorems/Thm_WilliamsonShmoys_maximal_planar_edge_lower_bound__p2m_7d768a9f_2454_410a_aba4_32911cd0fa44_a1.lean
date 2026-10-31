-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:12:05.43203+00:00
-- url     : https://prove2.me/theorems/a2753149-6560-4e8a-9416-1a8ad9b1c226
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has at least 3|V|−6 edges. A proof route is to extend its drawing to a triangulation on the same vertices, then use maximality to identify the extension with H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  sorry
