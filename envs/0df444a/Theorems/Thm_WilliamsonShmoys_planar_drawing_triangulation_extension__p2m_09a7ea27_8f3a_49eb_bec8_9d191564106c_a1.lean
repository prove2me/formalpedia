-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_09a7ea27_8f3a_49eb_bec8_9d191564106c_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_09a7ea27_8f3a_49eb_bec8_9d191564106c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:08.462993+00:00
-- url     : https://prove2.me/theorems/4cc4094d-71c5-4a34-a593-dbe980be82f8
-- title:
--   Triangulating a planar drawing by adding edges
-- statement:
--   Every finite simple graph with a planar drawing and at least three vertices has a planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_09a7ea27_8f3a_49eb_bec8_9d191564106c_a1 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
