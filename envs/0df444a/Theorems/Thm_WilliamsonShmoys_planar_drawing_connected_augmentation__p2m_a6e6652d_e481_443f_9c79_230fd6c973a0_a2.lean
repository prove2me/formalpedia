-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:17:13.51672+00:00
-- url     : https://prove2.me/theorems/87706138-1b1b-4896-af61-3aff6d2d47f5
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Any finite simple graph on at least three ordered vertices with a crossing-free drawing has a connected simple supergraph on the same vertices that also has a crossing-free drawing. The vertex-count hypothesis excludes the empty boundary case; isolated vertices and disconnected drawings are allowed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
