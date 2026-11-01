-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
-- name    : WilliamsonShmoys.planar_drawing_induce__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:56.029199+00:00
-- url     : https://prove2.me/theorems/ba96835b-a90c-4a63-85d8-6813e588e706
-- title:
--   Induced subgraphs inherit planar drawings
-- statement:
--   Restricting a planar drawing to a subset gives a planar drawing of its induced subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induce__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (A : Set V)
    [Fintype A] [LinearOrder A]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce A) := by sorry
