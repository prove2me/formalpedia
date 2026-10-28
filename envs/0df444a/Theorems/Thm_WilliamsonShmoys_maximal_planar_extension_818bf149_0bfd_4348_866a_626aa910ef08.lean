-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_818bf149_0bfd_4348_866a_626aa910ef08
-- name    : WilliamsonShmoys.maximal_planar_extension_818bf149_0bfd_4348_866a_626aa910ef08
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:25:54.238976+00:00
-- url     : https://prove2.me/theorems/2d7549fd-d75c-41ef-ad9e-25b5fe07b603
-- title:
--   Extension to a maximal drawable supergraph
-- statement:
--   A drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension_818bf149_0bfd_4348_866a_626aa910ef08
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U →
        WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
