-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:49:41.780955+00:00
-- url     : https://prove2.me/theorems/765f79d2-80fc-4ea0-854a-5bf0163b6a16
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. Prove this by deriving a plane embedding from the supplied crossing-free drawing, showing maximality forces connectedness and triangular faces, and applying Euler’s formula. The hypothesis |V| ≥ 3 is essential to this exact formula and includes the n=3 boundary; it is preserved explicitly. This child contains the remaining topological core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
