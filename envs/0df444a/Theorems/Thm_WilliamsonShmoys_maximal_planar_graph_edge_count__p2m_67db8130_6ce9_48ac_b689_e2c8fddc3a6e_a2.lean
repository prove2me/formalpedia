-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:04:33.024017+00:00
-- url     : https://prove2.me/theorems/6582e0a3-76e8-4a07-8065-8715ca29a41a
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
