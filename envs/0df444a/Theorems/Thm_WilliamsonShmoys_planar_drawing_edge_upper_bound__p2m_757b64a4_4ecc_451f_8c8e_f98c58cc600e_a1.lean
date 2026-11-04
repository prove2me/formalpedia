-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:27:09.933229+00:00
-- url     : https://prove2.me/theorems/711cef84-2190-482b-bc2d-a11a812cbece
-- title:
--   The planar simple graph edge bound
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
