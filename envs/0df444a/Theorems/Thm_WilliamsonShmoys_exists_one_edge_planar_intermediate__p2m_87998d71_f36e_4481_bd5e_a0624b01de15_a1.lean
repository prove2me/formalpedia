-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_one_edge_planar_intermediate__p2m_87998d71_f36e_4481_bd5e_a0624b01de15_a1
-- name    : WilliamsonShmoys.exists_one_edge_planar_intermediate__p2m_87998d71_f36e_4481_bd5e_a0624b01de15_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:25:36.869987+00:00
-- url     : https://prove2.me/theorems/bc1101b7-4ecc-4921-bd00-cf3198687379
-- title:
--   A proper drawable supergraph contains a one-edge drawable intermediate graph
-- statement:
--   For finite ordered vertex types, if K is a proper subgraph of a drawable graph L, then there is an intermediate graph M containing K and contained in L, drawable with exactly one more edge than K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_one_edge_planar_intermediate__p2m_87998d71_f36e_4481_bd5e_a0624b01de15_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (hKL : K ≤ L)
    (hKneL : K ≠ L)
    (hDrawL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, K ≤ M ∧ M ≤ L ∧
      M.edgeSet.ncard = K.edgeSet.ncard + 1 ∧
      WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
