-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:37.241248+00:00
-- url     : https://prove2.me/theorems/bb030fc9-0317-496e-aee9-1032f339651c
-- title:
--   Extend a planar drawing to an edge-maximal planar supergraph
-- statement:
--   A graph with a planar drawing on a finite linearly ordered vertex type has a planar supergraph on that same vertex type that has no strictly larger planar supergraph. There are only finitely many simple graphs on the fixed vertex type, so one can maximize the edge count among planar supergraphs containing the given graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := dH
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      H <= L ∧ HasPlanarDrawingOn L ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        L <= K → HasPlanarDrawingOn K → K = L) := by sorry
