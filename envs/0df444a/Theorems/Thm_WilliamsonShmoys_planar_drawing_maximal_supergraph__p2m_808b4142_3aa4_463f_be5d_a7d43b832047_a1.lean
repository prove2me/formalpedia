-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:12:53.131322+00:00
-- url     : https://prove2.me/theorems/0b957ae5-5ec4-449c-821a-692ecf51e4ba
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → L = H := by sorry
