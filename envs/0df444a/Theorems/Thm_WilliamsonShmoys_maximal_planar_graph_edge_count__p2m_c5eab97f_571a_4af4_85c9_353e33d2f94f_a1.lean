-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:11.918578+00:00
-- url     : https://prove2.me/theorems/438c2037-6b64-401b-a3fa-84e1ccf42d6c
-- title:
--   Euler edge count for maximal drawable planar graphs
-- statement:
--   An inclusion-maximal finite simple graph with a crossing-free drawing and at least three vertices has exactly `3|V|−6` edges. The independent proof route is to show maximality forces connectedness and triangular faces, then use Euler’s formula and count face-edge incidences. This is the main topological proof obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K' : SimpleGraph V, K ≤ K' →
      WilliamsonShmoys.HasPlanarDrawingOn K' → K' = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
