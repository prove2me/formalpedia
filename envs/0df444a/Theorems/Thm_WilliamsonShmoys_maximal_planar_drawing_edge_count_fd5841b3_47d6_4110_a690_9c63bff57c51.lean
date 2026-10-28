-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_fd5841b3_47d6_4110_a690_9c63bff57c51
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_fd5841b3_47d6_4110_a690_9c63bff57c51
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:38:28.571138+00:00
-- url     : https://prove2.me/theorems/fd0ff20a-6139-4c36-9311-863b106d3327
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable edge extensions has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_fd5841b3_47d6_4110_a690_9c63bff57c51
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      Q ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M ≤ Q) :
    3 * Fintype.card V - 6 = Q.edgeSet.ncard := by sorry
