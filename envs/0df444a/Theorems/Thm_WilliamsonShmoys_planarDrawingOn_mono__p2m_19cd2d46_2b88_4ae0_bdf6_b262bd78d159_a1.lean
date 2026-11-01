-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
-- name    : WilliamsonShmoys.planarDrawingOn_mono__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:06.141209+00:00
-- url     : https://prove2.me/theorems/b2953296-3496-4979-ac11-0e408e46e606
-- title:
--   Planarity is inherited by spanning subgraphs
-- statement:
--   A crossing-free drawing of a graph also witnesses a crossing-free drawing of any spanning subgraph, since the latter has only edges already represented in the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_mono__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsub : ∀ a b, H.Adj a b → G.Adj a b) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
