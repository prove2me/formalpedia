-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected_extension__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
-- name    : WilliamsonShmoys.planar_edge_bound_connected_extension__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:25.492993+00:00
-- url     : https://prove2.me/theorems/4c96a5c1-4d9b-4caf-9528-4938b1c228f4
-- title:
--   Connect a planar drawing without losing edges
-- statement:
--   Every finite planar drawing on the given vertex type can be extended to a connected planar graph on that same vertex type, containing the original graph and having at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_connected_extension__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧ K.Connected ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
