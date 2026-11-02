-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_with_maximal_edge_count__p2m_2f6efb11_cffe_4335_a64a_833cc169dca5_a2
-- name    : WilliamsonShmoys.planar_completion_with_maximal_edge_count__p2m_2f6efb11_cffe_4335_a64a_833cc169dca5_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:12:48.352936+00:00
-- url     : https://prove2.me/theorems/9bca3399-bc88-49f7-b83e-2aaaeb9cb6a3
-- title:
--   Planar graphs extend to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_with_maximal_edge_count__p2m_2f6efb11_cffe_4335_a64a_833cc169dca5_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V), HasPlanarDrawingOn L ∧
      ∃ (dL : DecidableRel L.Adj),
        (letI : DecidableRel L.Adj := dL;
          K.edgeFinset ⊆ L.edgeFinset ∧
          L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
