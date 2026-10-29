-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:38:22.448797+00:00
-- url     : https://prove2.me/theorems/898d49ba-9dbd-43ed-a27c-84bf5e276171
-- title:
--   Planar drawing edge bound for this target
-- statement:
--   Every graph with a drawing satisfying the attached predicate and at least three vertices has at most 3|V| − 6 edges. This removes the universal planar edge-count bound from the parent. Prove it by extending the drawing to a connected triangulated embedding on the same vertex set, applying Euler’s formula, and counting edge-face incidences; handle disconnected drawings when establishing the extension. The topological extension argument for the exact arc predicate remains open.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
