-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:30.373041+00:00
-- url     : https://prove2.me/theorems/3bfd1cbe-f3e5-4d66-8f6f-ed3e144b559b
-- title:
--   Finite maximal drawable supergraph exists
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under inclusion. This removes the finite maximization step from the parent; an independent proof route is to maximize edge count over the finite, nonempty collection of drawable supergraphs of the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
