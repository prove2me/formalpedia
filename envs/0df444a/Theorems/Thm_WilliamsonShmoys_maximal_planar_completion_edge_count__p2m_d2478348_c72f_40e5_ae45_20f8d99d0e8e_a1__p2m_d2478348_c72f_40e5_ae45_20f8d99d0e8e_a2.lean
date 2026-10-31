-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a1__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a2
-- name    : WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a1__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:44:22.391618+00:00
-- url     : https://prove2.me/theorems/285f4c6c-dc57-457d-a980-623bf68eff4b
-- title:
--   Planar completion to the maximal planar edge count
-- statement:
--   Every graph with the specified planar drawing on a finite linearly ordered vertex type of size at least three has a planar supergraph on the same vertex set with exactly 3|V|−6 edges. This isolates the geometric completion and Euler-counting work from the parent’s maximality argument. A proof route is to extend the drawing to a triangulation and count edge-face incidences using Euler’s formula; the three-vertex boundary case is covered by the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a1__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a2 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V) : ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧ T <= K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
