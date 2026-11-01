-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:16.830004+00:00
-- url     : https://prove2.me/theorems/c14196a8-6e2b-49b7-be83-e3c089778d01
-- title:
--   Extend a planar drawing to an edge-maximal planar graph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel H.Adj := dH
       K.edgeFinset ⊆ H.edgeFinset) ∧
      HasPlanarDrawingOn H ∧
      ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
        HasPlanarDrawingOn G →
        (letI : DecidableRel H.Adj := dH
         letI : DecidableRel G.Adj := dG
         H.edgeFinset ⊆ G.edgeFinset → H.edgeFinset = G.edgeFinset) := by
  sorry
