-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a1
-- name    : WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:24:49.731464+00:00
-- url     : https://prove2.me/theorems/08ca139c-aa81-496f-99a1-1a35bd0f101a
-- title:
--   Planar completion to the maximal planar edge count
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type of size at least three has a planar supergraph on that same vertex type with exactly 3|V|-6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V) : ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧ T ≤ K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
