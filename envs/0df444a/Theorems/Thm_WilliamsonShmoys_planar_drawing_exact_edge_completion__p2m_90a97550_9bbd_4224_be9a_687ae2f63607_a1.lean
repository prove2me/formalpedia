-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_completion__p2m_90a97550_9bbd_4224_be9a_687ae2f63607_a1
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_90a97550_9bbd_4224_be9a_687ae2f63607_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:26.712388+00:00
-- url     : https://prove2.me/theorems/55edef6f-d8c2-4514-97bb-024e1dcb6408
-- title:
--   Triangulation completion for a finite planar drawing
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. The claim includes disconnected drawings and the three-vertex case. It removes the geometric completion and exact edge-count work from the parent; the parent's maximality and finite graph order then force the original graph to equal this completion. A proof route is to form the finite plane embedding specified by the drawing arcs, connect components within faces as needed, add noncrossing diagonals until every face is triangular, and apply Euler's formula together with face-edge incidence counting. The remaining core obligation is formalizing faces, safe augmentation, and Euler counting from the given arc predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_90a97550_9bbd_4224_be9a_687ae2f63607_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, ∃ hMdec : DecidableRel M.Adj,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
