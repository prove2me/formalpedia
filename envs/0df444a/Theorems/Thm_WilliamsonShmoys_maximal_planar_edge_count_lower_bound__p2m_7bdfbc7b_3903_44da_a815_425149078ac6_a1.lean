-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:05:20.751613+00:00
-- url     : https://prove2.me/theorems/b83083f9-5b98-4643-9156-0c35319b256b
-- title:
--   Maximal planar graph edge-count lower bound
-- statement:
--   Every maximal drawable finite simple graph with at least three vertices has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeFinset.card + 6 := by
  sorry
