-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulating_extension_lower_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
-- name    : WilliamsonShmoys.planar_triangulating_extension_lower_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:40.741207+00:00
-- url     : https://prove2.me/theorems/ed0fa66f-dbcb-4794-9398-c71658f4fffe
-- title:
--   Triangulating extension on the same vertex set
-- statement:
--   Any drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set with at least 3|V| − 6 edges. The proof route extends the drawing to a maximal planar graph, whose faces are triangles; for three vertices the extension is K₃. The explicit adjacency instance on N makes its finite edge count well-formed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulating_extension_lower_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      exists N : SimpleGraph V,
        G <= N /\ HasPlanarDrawingOn N /\
          (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
            3 * Fintype.card V <= N.edgeFinset.card + 6)) := by sorry
