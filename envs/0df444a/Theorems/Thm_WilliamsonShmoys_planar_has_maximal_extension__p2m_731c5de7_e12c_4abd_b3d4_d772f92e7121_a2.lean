-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_has_maximal_extension__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
-- name    : WilliamsonShmoys.planar_has_maximal_extension__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:56:57.468984+00:00
-- url     : https://prove2.me/theorems/2a67879f-ce4b-4f0e-bdc9-1324812ff0fd
-- title:
--   Every drawable finite graph has a maximal drawable extension
-- statement:
--   Every drawable simple graph on a finite vertex type has a drawable supergraph on that same type that is maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_has_maximal_extension__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet →
        HasPlanarDrawingOn N → Set.Subset N.edgeSet M.edgeSet := by
  sorry
