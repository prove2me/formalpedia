-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:06:36.0732+00:00
-- url     : https://prove2.me/theorems/af21b660-e263-41f3-a209-fea21d5ace1b
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal under drawable edge-set extension, and whose edge count is at least the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      K.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet ⊆ M.edgeSet := by sorry
