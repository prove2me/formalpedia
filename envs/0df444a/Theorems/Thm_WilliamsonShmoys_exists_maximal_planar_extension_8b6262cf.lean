-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_8b6262cf
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_8b6262cf
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:30:38.130866+00:00
-- url     : https://prove2.me/theorems/4a839751-8e67-4385-97d1-fa29583bc764
-- title:
--   A finite drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension_8b6262cf
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ H : SimpleGraph V,
        L.edgeSet ⊆ H.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        L.edgeSet = H.edgeSet := by sorry
