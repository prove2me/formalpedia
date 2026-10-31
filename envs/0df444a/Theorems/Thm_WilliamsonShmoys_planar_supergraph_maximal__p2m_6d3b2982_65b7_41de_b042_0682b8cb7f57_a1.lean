-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:48:25.405034+00:00
-- url     : https://prove2.me/theorems/cc27f208-e691-45a3-b829-1ff8ad969310
-- title:
--   Existence of a maximum drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type whose edge count is at least that of every drawable supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V,
        P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q →
          Q.edgeSet.ncard ≤ P.edgeSet.ncard := by sorry
