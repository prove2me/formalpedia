-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_card_drawable_extension
-- name    : WilliamsonShmoys.exists_max_card_drawable_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:13:58.07268+00:00
-- url     : https://prove2.me/theorems/b0aafa9d-9401-4f12-82d2-4251d6f36276
-- title:
--   A drawable extension of maximum edge cardinality exists
-- statement:
--   Among drawable graphs on the finite vertex type that extend Q, there is one whose edge set has maximum cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_max_card_drawable_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      Set.Subset Q.edgeSet R.edgeSet ∧
      ∀ S : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn S →
        Set.Subset Q.edgeSet S.edgeSet →
        S.edgeSet.ncard ≤ R.edgeSet.ncard := by
  sorry
