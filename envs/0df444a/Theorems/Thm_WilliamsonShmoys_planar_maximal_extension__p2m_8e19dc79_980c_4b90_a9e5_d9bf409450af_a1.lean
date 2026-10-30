-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:33.181041+00:00
-- url     : https://prove2.me/theorems/4274c3cc-8877-4dcd-9fb0-968a87bc56a7
-- title:
--   A drawable graph has an inclusion-maximal drawable extension
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
