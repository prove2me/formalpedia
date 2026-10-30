-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:03.538916+00:00
-- url     : https://prove2.me/theorems/834425e9-b96f-42af-82f3-183711eb71b2
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A maximal planar simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
