-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_maximal_extension__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
-- name    : WilliamsonShmoys.planar_graph_maximal_extension__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:26.606279+00:00
-- url     : https://prove2.me/theorems/7793594c-aadb-4407-9b10-d0dd43a77b6e
-- title:
--   Maximal planar supergraph extension
-- statement:
--   Every finite graph with a crossing-free drawing has a maximal drawable supergraph on the same vertex type, with at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_maximal_extension__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry
