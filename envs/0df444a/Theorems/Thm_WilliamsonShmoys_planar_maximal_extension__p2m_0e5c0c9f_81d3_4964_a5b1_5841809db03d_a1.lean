-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:59.447207+00:00
-- url     : https://prove2.me/theorems/d574e4b0-8a82-440f-8f12-79d0cf0e5a52
-- title:
--   Existence of an inclusion-maximal planar extension
-- statement:
--   Every graph with a crossing-free drawing on a finite vertex set is contained in a graph on the same vertex set that has a crossing-free drawing and is maximal among its planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by sorry
