-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_8f423fe5_b3be_4138_81a9_17669ac64a5c_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_8f423fe5_b3be_4138_81a9_17669ac64a5c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:19.322435+00:00
-- url     : https://prove2.me/theorems/f1c5cd14-5ded-4838-bd8a-1ed332d55054
-- title:
--   Drawable graphs admit an exact maximal planar completion
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_8f423fe5_b3be_4138_81a9_17669ac64a5c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    exists H : SimpleGraph V, exists instH : DecidableRel H.Adj,
      (letI : DecidableRel H.Adj := instH
       G.edgeFinset ⊆ H.edgeFinset /\
       HasPlanarDrawingOn H /\
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
