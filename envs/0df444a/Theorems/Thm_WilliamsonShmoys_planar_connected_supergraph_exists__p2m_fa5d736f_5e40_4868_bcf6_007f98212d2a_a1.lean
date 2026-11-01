-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
-- name    : WilliamsonShmoys.planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:58.717403+00:00
-- url     : https://prove2.me/theorems/16c0a86c-fb19-4cdc-ad74-b712f6c195e0
-- title:
--   Connect a planar graph without adding vertices
-- statement:
--   Given the target’s crossing-free drawing, connect its components with noncrossing arcs to obtain a connected planar supergraph on the same vertices. This removes disconnected-component bookkeeping from the parent. A proof route is to connect embedded components iteratively through complementary regions, choosing arcs whose interiors avoid the existing finite drawing. The empty, singleton, and already connected cases must also be handled.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
