-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_6f64e769_ed8d_4f23_84ce_0685c66257bc_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_6f64e769_ed8d_4f23_84ce_0685c66257bc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:52.55431+00:00
-- url     : https://prove2.me/theorems/dca020c8-0d34-4686-be05-11734a76dced
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal graph with a crossing-free drawing on a finite ordered vertex set of size at least three has exactly three times the number of vertices minus six edges. The proof route is to show maximality forces a connected triangulation, then count vertices, edges, and triangular faces using Euler’s formula. This is stronger than the parent’s lower bound and reusable for edge-count results about maximal planar graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_6f64e769_ed8d_4f23_84ce_0685c66257bc_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hMax : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q) (hV : 3 ≤ Fintype.card V) : Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
