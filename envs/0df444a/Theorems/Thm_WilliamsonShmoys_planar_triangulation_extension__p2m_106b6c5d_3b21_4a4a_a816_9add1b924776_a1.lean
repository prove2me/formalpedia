-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_106b6c5d_3b21_4a4a_a816_9add1b924776_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_106b6c5d_3b21_4a4a_a816_9add1b924776_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:19.922079+00:00
-- url     : https://prove2.me/theorems/7aa49e78-992e-47a4-a47f-24fc3e2cd1e1
-- title:
--   Triangulation extension of a connected planar drawing
-- statement:
--   Every connected drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_106b6c5d_3b21_4a4a_a816_9add1b924776_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ G : SimpleGraph V,
      K.edgeFinset ⊆ G.edgeFinset ∧
      HasPlanarDrawingOn G ∧
      G.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
