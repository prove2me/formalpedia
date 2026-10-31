-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
-- name    : WilliamsonShmoys.maximal_drawable_connected__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:13.299679+00:00
-- url     : https://prove2.me/theorems/3e4841aa-5cc8-43c5-ada3-9b4132733a6e
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on a finite ordered vertex type of at least three vertices is connected. If the drawing has multiple components, a bridge can be added between components while preserving planarity, contradicting maximality. This isolates the connectivity argument needed before applying planar completion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_connected__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ H : SimpleGraph V, L ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L)
    (hV : 3 ≤ Fintype.card V) :
    L.Connected := by
  sorry
