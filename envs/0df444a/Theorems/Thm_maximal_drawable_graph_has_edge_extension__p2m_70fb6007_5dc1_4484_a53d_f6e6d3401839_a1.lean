-- Prove2me | Theorems.Thm_maximal_drawable_graph_has_edge_extension__p2m_70fb6007_5dc1_4484_a53d_f6e6d3401839_a1
-- name    : maximal_drawable_graph_has_edge_extension__p2m_70fb6007_5dc1_4484_a53d_f6e6d3401839_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:24:35.229761+00:00
-- url     : https://prove2.me/theorems/869ffda5-b864-4783-a885-44fd746ff24a
-- title:
--   A drawable graph below the planar edge bound has a drawable strict extension
-- statement:
--   On a finite linearly ordered vertex type with at least three vertices, any drawable graph with fewer than 3|V|−6 edges has a drawable strict supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem maximal_drawable_graph_has_edge_extension__p2m_70fb6007_5dc1_4484_a53d_f6e6d3401839_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := dK
    K.edgeFinset.card < 3 * Fintype.card V - 6 →
      ∃ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L ∧ K ≤ L ∧ ¬ L ≤ K := by
  sorry
