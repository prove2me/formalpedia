-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_d908ff8e_b2ea_4f26_9ee5_97f35f4c9df1_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_d908ff8e_b2ea_4f26_9ee5_97f35f4c9df1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:59:26.866364+00:00
-- url     : https://prove2.me/theorems/bf560835-e420-42cf-80f6-9c119aabf70e
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs, and the original edge count is at most the maximal graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_d908ff8e_b2ea_4f26_9ee5_97f35f4c9df1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       L.edgeFinset.card ≤ M.edgeSet.ncard) := by sorry
