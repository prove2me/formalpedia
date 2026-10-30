-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T19:03:10.995514+00:00
-- url     : https://prove2.me/theorems/a86a1baa-47e2-48fa-862c-090c2103970c
-- title:
--   Planar extension from an unreachable pair
-- statement:
--   Given a supplied planar drawing and two vertices in different components, there is a strict planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hsep : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V, G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
