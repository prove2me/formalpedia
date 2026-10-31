-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count__p2m_078165f8_2282_4c2b_9ab6_7e9aed87e1a3_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_078165f8_2282_4c2b_9ab6_7e9aed87e1a3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:22:22.238997+00:00
-- url     : https://prove2.me/theorems/98c8cf30-bc8e-4089-995f-e52a299a85f1
-- title:
--   Planar triangulation completion with fixed vertex set
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This is the fixed-vertex planar triangulation completion result. It removes the geometric completion and Euler-count work from the parent; the parent applies maximality to the extension and substitutes the resulting equality. A proof route is to complete the drawing by adding noncrossing diagonals until its faces are triangles, then derive the edge count from Euler’s formula and the fact that each edge borders two face sides. The central remaining work is formalizing face structure and this completion process for the supplied continuous-arc definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_078165f8_2282_4c2b_9ab6_7e9aed87e1a3_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 <= Fintype.card V) : ∃ N : SimpleGraph V, LE.le M N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
