-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_00187ed1_118c_4569_ae21_cc59aa929691
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_extension_00187ed1_118c_4569_ae21_cc59aa929691
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:27:40.138933+00:00
-- url     : https://prove2.me/theorems/3cacabb3-2060-4a51-bdbf-8cf76cf66eee
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every finite graph with a planar drawing has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_extension_00187ed1_118c_4569_ae21_cc59aa929691
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by sorry
