-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:48.707857+00:00
-- url     : https://prove2.me/theorems/e4274472-fa7f-45c2-bc46-56de2add020a
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices with no strict drawable supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
