-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_6c35d7b0_b5ac_47cb_81ba_67341f778754_a1
-- name    : WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_6c35d7b0_b5ac_47cb_81ba_67341f778754_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:31.412819+00:00
-- url     : https://prove2.me/theorems/475324d9-e323-4e9d-912b-397241bc4fc3
-- title:
--   Finite maximal planar supergraph
-- statement:
--   Every planar graph on a finite linearly ordered vertex type has an inclusion-maximal planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_6c35d7b0_b5ac_47cb_81ba_67341f778754_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L →
        ¬ K.edgeSet ⊂ L.edgeSet := by sorry
