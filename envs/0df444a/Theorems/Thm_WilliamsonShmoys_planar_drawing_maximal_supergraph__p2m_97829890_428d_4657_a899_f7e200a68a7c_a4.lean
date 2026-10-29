-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:27:20.809409+00:00
-- url     : https://prove2.me/theorems/3ad60fc3-1bed-4725-aaf6-264d650d407f
-- title:
--   A finite maximal drawable supergraph exists
-- statement:
--   Among the drawable supergraphs of a finite graph on the same ordered vertex type, one is maximal under graph inclusion. This removes the finite selection step from the parent proof; maximize edge count over all drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
