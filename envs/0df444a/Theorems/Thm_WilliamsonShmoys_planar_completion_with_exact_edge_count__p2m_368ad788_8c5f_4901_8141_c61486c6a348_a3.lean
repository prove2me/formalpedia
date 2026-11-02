-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_with_exact_edge_count__p2m_368ad788_8c5f_4901_8141_c61486c6a348_a3
-- name    : WilliamsonShmoys.planar_completion_with_exact_edge_count__p2m_368ad788_8c5f_4901_8141_c61486c6a348_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:02:37.18765+00:00
-- url     : https://prove2.me/theorems/85c2c346-28e5-4534-9163-3ad06b60ce35
-- title:
--   Exact edge count for a planar completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_with_exact_edge_count__p2m_368ad788_8c5f_4901_8141_c61486c6a348_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V), ∃ (dK : DecidableRel K.Adj),
      N ≤ K ∧ HasPlanarDrawingOn K ∧
        (letI : DecidableRel K.Adj := dK;
          3 * Fintype.card V = K.edgeFinset.card + 6) := by sorry
