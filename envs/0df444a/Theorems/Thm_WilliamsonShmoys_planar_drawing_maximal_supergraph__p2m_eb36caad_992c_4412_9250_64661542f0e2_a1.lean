-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:30:47.19661+00:00
-- url     : https://prove2.me/theorems/b63b564c-76d3-404f-8235-1d60938cc4b1
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every finite graph with a planar drawing has an inclusion-maximal planar supergraph on the same vertex type, and the supergraph has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧
      HasPlanarDrawingOn K' ∧
      (∀ L : SimpleGraph V, K' ≤ L → HasPlanarDrawingOn L → L ≤ K') ∧
      K.edgeSet.ncard ≤ K'.edgeSet.ncard := by sorry
