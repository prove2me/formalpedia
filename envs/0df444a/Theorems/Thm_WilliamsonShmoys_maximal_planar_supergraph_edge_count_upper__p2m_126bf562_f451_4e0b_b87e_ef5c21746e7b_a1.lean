-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:39.921167+00:00
-- url     : https://prove2.me/theorems/c170bf8c-b2d9-4b02-9b98-b3f4410d9192
-- title:
--   Planar graph edge-count upper bound
-- statement:
--   Any graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This isolates the Euler-formula and face-incidence argument needed for the upper inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P) :
    (letI : DecidableRel P.Adj := Classical.decRel P.Adj;
      P.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
