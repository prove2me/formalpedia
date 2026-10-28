-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:21:17.748281+00:00
-- url     : https://prove2.me/theorems/f4cb8c05-b66d-460b-b025-904e9a860d95
-- title:
--   Edge count of a maximal finite planar drawing
-- statement:
--   A finite simple graph on at least three vertices whose drawing cannot be extended by adding edges has exactly `3|V| - 6` edges. A proof route is to show that maximality forces every face in the associated planar embedding to be triangular, then count edge-face incidences and apply Euler’s formula. The `|V| ≥ 3` hypothesis is essential for this equality; this child supplies the planar counting core used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet = K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
