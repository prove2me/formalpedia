-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:18.394093+00:00
-- url     : https://prove2.me/theorems/626039db-5057-4194-82d1-e074d68da7fd
-- title:
--   Count the edges of an edge-maximal planar graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable edge extensions has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
      HasPlanarDrawingOn G →
      (letI : DecidableRel H.Adj := dH
       letI : DecidableRel G.Adj := dG
       H.edgeFinset ⊆ G.edgeFinset → H.edgeFinset = G.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := dH
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry
