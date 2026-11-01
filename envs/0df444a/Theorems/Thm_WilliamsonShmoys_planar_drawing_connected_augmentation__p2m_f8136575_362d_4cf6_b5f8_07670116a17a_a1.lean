-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:00.608331+00:00
-- url     : https://prove2.me/theorems/f2188066-bdee-41e3-86df-42250492e63d
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Any finite graph with the given crossing-free drawing has a connected planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
