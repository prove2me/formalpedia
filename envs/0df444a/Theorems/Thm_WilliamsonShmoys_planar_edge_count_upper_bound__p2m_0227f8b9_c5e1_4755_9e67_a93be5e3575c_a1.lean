-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:42.921445+00:00
-- url     : https://prove2.me/theorems/09ac247b-fe9e-49f3-a563-2231c8d12f27
-- title:
--   Planar edge count upper bound
-- statement:
--   Every graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. Prove this by relating vertices, edges, and faces through Euler's formula and using that each face boundary contributes at least three edge-sides (with the small or degenerate cases handled explicitly). This provides the upper inequality independently of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
    Q.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
