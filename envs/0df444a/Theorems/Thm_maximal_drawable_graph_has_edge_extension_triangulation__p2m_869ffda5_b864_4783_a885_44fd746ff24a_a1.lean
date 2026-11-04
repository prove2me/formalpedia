-- Prove2me | Theorems.Thm_maximal_drawable_graph_has_edge_extension_triangulation__p2m_869ffda5_b864_4783_a885_44fd746ff24a_a1
-- name    : maximal_drawable_graph_has_edge_extension_triangulation__p2m_869ffda5_b864_4783_a885_44fd746ff24a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:32:17.891693+00:00
-- url     : https://prove2.me/theorems/d8aa4474-1bb0-4a8a-92a2-795d49f289c9
-- title:
--   Every drawable graph extends to a triangulation
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, a drawable graph with fewer than 3|V|−6 edges has a drawable strict supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem maximal_drawable_graph_has_edge_extension_triangulation__p2m_869ffda5_b864_4783_a885_44fd746ff24a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := dK
    K.edgeFinset.card < 3 * Fintype.card V - 6 →
      ∃ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L ∧ K ≤ L ∧ ¬ L ≤ K ∧
          (letI : DecidableRel L.Adj := Classical.decRel L.Adj
           L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry
