-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:44:48.109493+00:00
-- url     : https://prove2.me/theorems/e898f611-daf1-4dfe-81ce-58fcea29a600
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every graph with a drawing has a drawable supergraph on the same finite vertex type that is maximal among drawable supergraphs under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
