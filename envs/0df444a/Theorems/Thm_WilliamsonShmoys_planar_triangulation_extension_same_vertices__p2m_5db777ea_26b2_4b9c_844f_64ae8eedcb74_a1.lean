-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_same_vertices__p2m_5db777ea_26b2_4b9c_844f_64ae8eedcb74_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_same_vertices__p2m_5db777ea_26b2_4b9c_844f_64ae8eedcb74_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:20:17.698991+00:00
-- url     : https://prove2.me/theorems/5aab7b66-88f9-4907-8957-a5a3c4b4addc
-- title:
--   Extension of a planar drawing to a triangulation
-- statement:
--   Every finite drawable simple graph on at least three fixed vertices has a drawable supergraph on the same vertex set whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_same_vertices__p2m_5db777ea_26b2_4b9c_844f_64ae8eedcb74_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V) : ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧ U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
