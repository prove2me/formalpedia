-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension__p2m_e364c09d_03b7_4604_b246_80ad4b3eeeb7_a4
-- name    : WilliamsonShmoys.planar_graph_triangulation_extension__p2m_e364c09d_03b7_4604_b246_80ad4b3eeeb7_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:02:10.042708+00:00
-- url     : https://prove2.me/theorems/8b952692-ce82-4b1a-b285-daef0e717378
-- title:
--   Triangulation extension for a planar drawing
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices can be extended, on the same vertex set, to a drawable triangulated graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_extension__p2m_e364c09d_03b7_4604_b246_80ad4b3eeeb7_a4 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
