-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_drawable_maximum_cardinality
-- name    : WilliamsonShmoys.finite_drawable_maximum_cardinality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:30:14.691969+00:00
-- url     : https://prove2.me/theorems/ea46019b-b515-4551-9f38-734cc03221d3
-- title:
--   Maximum cardinality drawable supergraph
-- statement:
--   Among all drawable graphs on the same finite vertex type that contain H, there is one whose edge set has maximum cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_drawable_maximum_cardinality
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        H.edgeSet ⊆ L.edgeSet →
        HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
