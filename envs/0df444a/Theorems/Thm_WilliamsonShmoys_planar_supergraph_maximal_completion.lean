-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_completion
-- name    : WilliamsonShmoys.planar_supergraph_maximal_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:49:21.329136+00:00
-- url     : https://prove2.me/theorems/25f8bb07-c8f5-492a-ab32-087fe619041d
-- title:
--   Existence of a maximal planar supergraph on the same vertex set
-- statement:
--   A planar graph on a finite vertex type has an inclusion-maximal planar supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        G.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by sorry
