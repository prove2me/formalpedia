-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augment_edge__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a2
-- name    : WilliamsonShmoys.planar_augment_edge__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:09:08.119975+00:00
-- url     : https://prove2.me/theorems/31eae51c-a022-4eed-a50e-3cb15ceb65ac
-- title:
--   One-edge augmentation of a planar drawing
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free drawing and fewer than 3|V|−6 edges can be extended on the same vertices by adding one edge while preserving a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augment_edge__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V)
    (hSize : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    Exists fun H : SimpleGraph V =>
      G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
        H.edgeSet.ncard = G.edgeSet.ncard + 1 := by sorry
