-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_20261026
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:20:32.846797+00:00
-- url     : https://prove2.me/theorems/f08ed7cb-c245-4afc-805c-f55816da3462
-- title:
--   Edge bound for a finite planar drawing
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the Euler upper-bound step. A proof route is to handle connected components, apply Euler’s formula to each nontrivial connected planar embedding, and count face-boundary incidences; the small tree and component cases satisfy the bound directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
