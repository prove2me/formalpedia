-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:21:16.027566+00:00
-- url     : https://prove2.me/theorems/af5ef936-754d-4f1b-a8c0-025d8e67bd44
-- title:
--   Maximal planar extension of a finite drawing
-- statement:
--   Every finite graph with a crossing-free drawing has a planar supergraph on the same vertices that is maximal under adding edges while preserving such a drawing. The subset condition preserves all original edges. A proof route is to order the finitely many possible edge sets by inclusion and choose a maximal drawable extension; the geometric existence argument must preserve the drawing condition as edges are added. This removes the finite maximal-extension step from the parent. The remaining core is proving the edge count of a maximal drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        H.edgeSet = K.edgeSet := by sorry
