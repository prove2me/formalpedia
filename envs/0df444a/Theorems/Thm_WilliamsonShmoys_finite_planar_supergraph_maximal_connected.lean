-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal_connected
-- name    : WilliamsonShmoys.finite_planar_supergraph_maximal_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:11:11.17069+00:00
-- url     : https://prove2.me/theorems/07aa7e0f-afd2-4a0e-9dd1-4e490f3e8f33
-- title:
--   Maximal planar supergraphs are connected when disconnected extensions exist
-- statement:
--   If every disconnected planar supergraph of a fixed finite graph has a strict planar extension, then the fixed graph has a connected planar supergraph whose edge count is at least as large. Choose a planar supergraph with maximal edge count from the finite set of graphs on the vertex type; the extension property forces it to be connected. The edge-count inequality follows from containment.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_supergraph_maximal_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hStep : ∀ K : SimpleGraph V,
      G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K < L ∧ WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
