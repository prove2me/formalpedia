-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:36.568713+00:00
-- url     : https://prove2.me/theorems/5b0c031e-8142-47ae-ab53-429c7b3c573a
-- title:
--   Edge lower bound for a maximal finite simple planar graph
-- statement:
--   If a finite simple graph on at least three vertices has a crossing-free drawing and cannot be extended to a strictly larger graph with such a drawing on the same vertex type, then it has at least 3n − 6 edges. Maximality rules out nontriangular faces; Euler’s formula and face-edge incidence yield the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7ce99e29_e187_4d62_b312_8a5637649ce2_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
