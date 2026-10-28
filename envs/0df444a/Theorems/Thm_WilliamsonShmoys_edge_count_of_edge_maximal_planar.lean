-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar
-- name    : WilliamsonShmoys.edge_count_of_edge_maximal_planar
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:38:20.758583+00:00
-- url     : https://prove2.me/theorems/e10b5efc-0142-4f75-9c52-ed33deba7e94
-- title:
--   An edge-count-maximal planar graph has 3n − 6 edges
-- statement:
--   A finite simple graph with at least three vertices whose planar drawing cannot be extended by adding edges has exactly 3|V| − 6 edges. A proof can establish connectedness and triangular faces for an edge-maximal planar embedding, then use Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_edge_maximal_planar
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
