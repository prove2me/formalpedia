-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:33:55.444306+00:00
-- url     : https://prove2.me/theorems/81062036-a3b3-4ed6-8d28-d9134310cf46
-- title:
--   Finite maximal planar extension
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertices that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
