-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
-- name    : WilliamsonShmoys.maximal_planar_upper_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:01.531693+00:00
-- url     : https://prove2.me/theorems/a60c0160-4029-4185-bfe8-ff4b14f19470
-- title:
--   Upper edge bound for a drawable simple graph
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_upper_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V) :
    L.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  sorry
