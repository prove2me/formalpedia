-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_drawable_extension__p2m_bb4dce47_9275_45c5_899b_6355cecbb075_a5
-- name    : WilliamsonShmoys.planar_drawing_maximal_drawable_extension__p2m_bb4dce47_9275_45c5_899b_6355cecbb075_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:25:36.589786+00:00
-- url     : https://prove2.me/theorems/081cacc4-373c-4910-a6b9-5c7ef350e4e2
-- title:
--   Maximal drawable extension on a finite vertex set
-- statement:
--   Every connected finite graph with a drawing on the plane’s point set has a supergraph on the same vertex set that remains drawable and connected, has at least as many edges, and is maximal among drawable supergraphs. The proof selects a graph with the largest edge count among the finitely many drawable supergraphs; connectedness and the lower bound follow from inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_drawable_extension__p2m_bb4dce47_9275_45c5_899b_6355cecbb075_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
