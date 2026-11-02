-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_cd005786_48c0_47b3_9c83_f93270ee4ea9_a2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_cd005786_48c0_47b3_9c83_f93270ee4ea9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:56:13.241709+00:00
-- url     : https://prove2.me/theorems/c094e1ea-128e-405b-80b1-7c29021d62f8
-- title:
--   Complete a drawable graph to a triangulation on the same vertices
-- statement:
--   Any graph with the specified crossing-free drawing and at least three vertices is contained, on the same vertex set, in a simple graph whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_cd005786_48c0_47b3_9c83_f93270ee4ea9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn G) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    Exists fun H : SimpleGraph V =>
      And (forall u v, G.Adj u v -> H.Adj u v)
        (H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
