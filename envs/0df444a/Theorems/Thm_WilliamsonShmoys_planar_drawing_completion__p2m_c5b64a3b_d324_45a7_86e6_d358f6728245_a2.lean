-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion__p2m_c5b64a3b_d324_45a7_86e6_d358f6728245_a2
-- name    : WilliamsonShmoys.planar_drawing_completion__p2m_c5b64a3b_d324_45a7_86e6_d358f6728245_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:39.954549+00:00
-- url     : https://prove2.me/theorems/89b917c7-2895-4f7d-ae75-caac4f55b041
-- title:
--   Completion of a finite planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion__p2m_c5b64a3b_d324_45a7_86e6_d358f6728245_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (J : SimpleGraph V) (dJ : DecidableRel J.Adj),
      G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
        (letI : DecidableRel J.Adj := dJ;
          J.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
