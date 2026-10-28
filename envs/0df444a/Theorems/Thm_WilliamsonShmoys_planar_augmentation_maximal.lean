-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal
-- name    : WilliamsonShmoys.planar_augmentation_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:07:16.613995+00:00
-- url     : https://prove2.me/theorems/a810bb22-ef6b-4865-acf7-f291a08de57f
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable graph
-- statement:
--   Every drawable graph on a finite vertex set of size at least three has a drawable supergraph on the same vertices that is maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_augmentation_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
        ∀ S : SimpleGraph V, R ≤ S →
          WilliamsonShmoys.HasPlanarDrawingOn S → S = R := by sorry
