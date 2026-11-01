-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:59.526403+00:00
-- url     : https://prove2.me/theorems/8532617a-0690-495a-a2cc-fdaf4080cf05
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that has a planar drawing and is maximal among planar supergraphs on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      T.edgeSet ⊆ U.edgeSet →
      (∃ e, e ∈ U.edgeSet ∧ e ∉ T.edgeSet) →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
