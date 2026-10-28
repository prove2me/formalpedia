-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_nat_edge_count_completion
-- name    : WilliamsonShmoys.planar_drawing_nat_edge_count_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:26:35.1245+00:00
-- url     : https://prove2.me/theorems/c3a2e3c2-e652-4e92-b8d8-625a935a4f7b
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V| − 6. At |V| = 3, the completion is the triangle; generally, the proof extends the drawing to a maximal planar drawing and counts its triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_nat_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      N ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
