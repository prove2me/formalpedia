-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:33:16.839542+00:00
-- url     : https://prove2.me/theorems/128bf6bf-2a09-471e-9b1c-d385c868d715
-- title:
--   A maximal drawable graph has the planar edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet → HasPlanarDrawingOn G → G.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
