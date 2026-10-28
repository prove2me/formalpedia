-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension_v2
-- name    : WilliamsonShmoys.exists_maximal_drawable_extension_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:26:44.358545+00:00
-- url     : https://prove2.me/theorems/a975287b-d970-443e-958c-bc5d812fd36d
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_extension_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZdraw : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V, Z ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W ≤ X →
        WilliamsonShmoys.HasPlanarDrawingOn X → X = W := by sorry
