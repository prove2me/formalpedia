-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_057ef142_41f3_41d0_8648_8115a105ce61
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_057ef142_41f3_41d0_8648_8115a105ce61
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:14:43.242632+00:00
-- url     : https://prove2.me/theorems/63e94e3e-2c21-4a4e-a905-7756aa47d05f
-- title:
--   Edge-set cardinality is monotone under inclusion
-- statement:
--   For finite simple graphs on the same finite vertex type, edge-set inclusion implies monotonicity of edge-set `ncard`. The finite vertex type ensures both edge sets are finite. This removes the cardinality step from the parent; it can be proved by converting edge sets to finite sets and applying finite-set cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono_057ef142_41f3_41d0_8648_8115a105ce61
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (h : Set.Subset G.edgeSet H.edgeSet) :
    G.edgeSet.ncard <= H.edgeSet.ncard := by sorry
