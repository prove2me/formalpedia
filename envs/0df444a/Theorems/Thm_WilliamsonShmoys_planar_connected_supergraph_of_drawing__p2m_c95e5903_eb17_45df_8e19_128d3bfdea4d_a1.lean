-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_of_drawing__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
-- name    : WilliamsonShmoys.planar_connected_supergraph_of_drawing__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:13.527498+00:00
-- url     : https://prove2.me/theorems/e04f1e17-20de-446c-b9b1-9c0568158af1
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Given a nonempty finite graph with a crossing-free drawing, there is a connected drawable supergraph on the same vertices whose edge count is at least as large. The child removes disconnectedness from the parent. A proof route is to connect the finitely many drawn components by arcs in complementary regions, preserving the existing drawing and edges. The remaining core is formalizing this topological augmentation for the given drawing predicate. The explicit local decidability instances make both finite edge counts well-typed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph_of_drawing__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hne : 0 < Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj
         letI : DecidableRel H.Adj := Classical.decRel H.Adj
         G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
