-- Prove2me | Theorems.Thm_planar_drawing_edge_upper_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
-- name    : planar_drawing_edge_upper_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:11:21.310881+00:00
-- url     : https://prove2.me/theorems/ff312b32-33bc-4641-9fb0-85a09241c514
-- title:
--   Euler upper bound for a drawn simple graph
-- statement:
--   Every finite simple graph on at least three vertices satisfying the given drawing predicate has at most 3n − 6 edges. The vertex lower bound excludes the small-vertex exceptions. A proof can connect the drawing’s components by noncrossing arcs and apply Euler’s formula and the simple-planar face bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem planar_drawing_edge_upper_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
