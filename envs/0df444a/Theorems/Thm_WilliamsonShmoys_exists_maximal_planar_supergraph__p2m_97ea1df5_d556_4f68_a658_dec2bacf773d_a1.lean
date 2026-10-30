-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:24.626394+00:00
-- url     : https://prove2.me/theorems/adb7eae7-2a82-406a-9d69-125f3f83074d
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   Any finite graph with a planar drawing is contained, on the same vertex type, in a drawable graph that has no strictly larger drawable supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
