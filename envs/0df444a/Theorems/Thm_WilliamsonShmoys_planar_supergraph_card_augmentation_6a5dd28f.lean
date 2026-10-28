-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_card_augmentation_6a5dd28f
-- name    : WilliamsonShmoys.planar_supergraph_card_augmentation_6a5dd28f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:57:17.755082+00:00
-- url     : https://prove2.me/theorems/4ed997be-00cf-4bdc-be9e-32df522d75cf
-- title:
--   A finite drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_card_augmentation_6a5dd28f {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
