-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:18.603372+00:00
-- url     : https://prove2.me/theorems/2a4e0817-5ede-4993-80da-c0938cce21b3
-- title:
--   A maximal planar graph on at least three vertices has 3n − 6 edges
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3n − 6 edges. A proof route is to show maximality forces connectedness and triangular faces, then formalize Euler’s formula and the face-degree count. For three vertices the result specializes to the triangle’s three edges. This child carries the remaining topological argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
