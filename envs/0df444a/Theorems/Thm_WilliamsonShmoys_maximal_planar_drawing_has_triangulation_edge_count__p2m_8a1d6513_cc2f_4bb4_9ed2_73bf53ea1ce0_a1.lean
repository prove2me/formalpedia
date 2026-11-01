-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:37.085476+00:00
-- url     : https://prove2.me/theorems/934dd260-db8f-4134-a45d-3b3ebead8b8e
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A connected drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    (∀ G : SimpleGraph V, K.edgeFinset ⊆ G.edgeFinset →
      HasPlanarDrawingOn G → G = K) →
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
