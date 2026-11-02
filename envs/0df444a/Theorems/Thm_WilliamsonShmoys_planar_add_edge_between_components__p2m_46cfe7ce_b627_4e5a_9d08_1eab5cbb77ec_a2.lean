-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components__p2m_46cfe7ce_b627_4e5a_9d08_1eab5cbb77ec_a2
-- name    : WilliamsonShmoys.planar_add_edge_between_components__p2m_46cfe7ce_b627_4e5a_9d08_1eab5cbb77ec_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:29:32.570861+00:00
-- url     : https://prove2.me/theorems/b1cb0656-cefe-4cc7-b652-354147c2b89b
-- title:
--   Adding an edge between distinct components preserves drawability
-- statement:
--   For two vertices in different components of a graph with the specified planar drawing, one can add their edge and obtain a drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_components__p2m_46cfe7ce_b627_4e5a_9d08_1eab5cbb77ec_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    {u v : V}
    (hnotReach : ¬ M.Reachable u v) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧ H.Adj u v ∧ HasPlanarDrawingOn H := by sorry
