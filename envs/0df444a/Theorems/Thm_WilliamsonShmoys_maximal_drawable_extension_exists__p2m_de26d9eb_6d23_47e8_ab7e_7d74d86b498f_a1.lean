-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_exists__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
-- name    : WilliamsonShmoys.maximal_drawable_extension_exists__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:01:21.698325+00:00
-- url     : https://prove2.me/theorems/808009b6-14af-4269-9066-05ec056856e1
-- title:
--   Every drawable graph has a maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension_exists__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
