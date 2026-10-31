-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:31.029984+00:00
-- url     : https://prove2.me/theorems/22c09847-b733-4661-b230-9655792a93fd
-- title:
--   Triangulated planar extension on the same vertex set
-- statement:
--   Any finite simple graph with at least three vertices that has a drawing satisfying the packaged noncrossing-arc predicate has a supergraph on the same vertices, also satisfying that predicate, with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
