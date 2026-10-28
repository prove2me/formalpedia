-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:23:55.083993+00:00
-- url     : https://prove2.me/theorems/58f50f87-0635-4cc8-b61d-9d1ec9455dbd
-- title:
--   Edge count monotonicity under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion implies edge-count monotonicity. Prove this by showing the first edge set is a subset of the second and applying finite-cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono_d42c8f91_ac47_4320_bc80_c3d77a1995cc
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
