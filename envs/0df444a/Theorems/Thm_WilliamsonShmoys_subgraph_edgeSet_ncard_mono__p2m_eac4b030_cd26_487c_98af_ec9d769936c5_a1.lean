-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_mono__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
-- name    : WilliamsonShmoys.subgraph_edgeSet_ncard_mono__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:00.675844+00:00
-- url     : https://prove2.me/theorems/c2a138fb-edf7-4e20-bfbf-2ecf01b29ef2
-- title:
--   Monotonicity of edge count under subgraph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, subgraph inclusion implies that the subgraph has no more edges. This removes the transfer step from H’s Euler bound to M in the parent. It follows by showing that M’s edge set is included in H’s edge set and using monotonicity of finite-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.subgraph_edgeSet_ncard_mono__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H) :
    M.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
