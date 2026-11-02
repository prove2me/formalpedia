-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_edge_set__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
-- name    : WilliamsonShmoys.planar_supergraph_maximal_edge_set__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:34:50.946286+00:00
-- url     : https://prove2.me/theorems/6ba26de6-69bc-4fed-ac6d-a483b85550c4
-- title:
--   Every finite drawable graph has an edge-maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that admits no strict drawable edge supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_edge_set__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V), HasPlanarDrawingOn L ∧
      ∃ (dL : DecidableRel L.Adj),
        (letI : DecidableRel L.Adj := dL;
          K.edgeFinset ⊆ L.edgeFinset ∧
          ∀ (M : SimpleGraph V) [DecidableRel M.Adj],
            HasPlanarDrawingOn M →
            L.edgeFinset ⊆ M.edgeFinset →
            M.edgeFinset ⊆ L.edgeFinset) := by sorry
