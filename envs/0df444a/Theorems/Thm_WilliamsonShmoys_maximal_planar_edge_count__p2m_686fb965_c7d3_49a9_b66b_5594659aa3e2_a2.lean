-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:40.083006+00:00
-- url     : https://prove2.me/theorems/4d9bb183-475b-4a59-8b75-1a8cda8dae1d
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A finite simple graph with at least three vertices that has a crossing-free drawing and admits no strictly larger planar supergraph on the same vertex type has exactly 3|V|−6 edges. The intended route is to show maximality forces triangular faces and then apply Euler’s formula; this includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      L <= K → HasPlanarDrawingOn K → K = L) :
    letI : DecidableRel L.Adj := dL
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
