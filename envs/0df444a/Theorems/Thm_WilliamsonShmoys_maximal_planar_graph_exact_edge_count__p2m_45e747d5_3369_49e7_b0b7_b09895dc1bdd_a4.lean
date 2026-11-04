-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
-- name    : WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:50:16.494198+00:00
-- url     : https://prove2.me/theorems/84b83a52-4380-4290-8494-df49bd55089b
-- title:
--   Exact edge count for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that admits no drawable edge extension on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      ∀ u v, P.Adj u v → N.Adj u v) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
