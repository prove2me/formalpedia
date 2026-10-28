-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_completion_maximal_planar_drawing_4f89c2
-- name    : WilliamsonShmoys.exists_completion_maximal_planar_drawing_4f89c2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:47:08.410855+00:00
-- url     : https://prove2.me/theorems/4650bba4-5869-4870-b521-0bb0918e1c90
-- title:
--   Existence of a maximal planar drawing completion
-- statement:
--   Any finite graph with the supplied planar drawing has a planar supergraph on the same vertex type that is maximal under strict edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_completion_maximal_planar_drawing_4f89c2
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q.edgeSet ⊆ R.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R.edgeSet ⊂ S.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn S := by sorry
