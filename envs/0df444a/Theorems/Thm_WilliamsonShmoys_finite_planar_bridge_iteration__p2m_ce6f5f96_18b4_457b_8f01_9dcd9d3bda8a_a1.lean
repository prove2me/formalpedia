-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_bridge_iteration__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
-- name    : WilliamsonShmoys.finite_planar_bridge_iteration__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:18:31.327992+00:00
-- url     : https://prove2.me/theorems/8b72fe1b-c6b2-4b74-bbc5-2cec97a3f29a
-- title:
--   Iterate strict planar edge extensions to connectivity
-- statement:
--   If every disconnected drawable supergraph of a finite drawable graph admits a strict drawable edge extension, then there is a connected drawable supergraph containing the initial graph, with at least as many edges. Prove this by maximizing edge count among the finitely many simple graphs on the vertex type; a disconnected maximizer would admit a strict extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_bridge_iteration__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hStep : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K ≤ L ∧ K.edgeSet ⊂ L.edgeSet ∧
        WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
