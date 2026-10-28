-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:55:12.127736+00:00
-- url     : https://prove2.me/theorems/cea57825-7fdd-43e2-80dd-a2413226a20d
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge-set cardinality is no larger. Prove by edge-set inclusion and monotonicity of finite cardinality. This removes the combinatorial counting step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
