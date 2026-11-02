-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:24:00.095769+00:00
-- url     : https://prove2.me/theorems/bbd04a1c-d297-4882-8984-b8714d7044d0
-- title:
--   Extend a drawable graph to an edge-maximal drawable graph
-- statement:
--   Any finite graph with the specified crossing-free drawing has an edge-maximal drawable supergraph on the same vertex set, and its edge count is no smaller.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := dH;
       letI : DecidableRel K.Adj := dK;
       H.edgeFinset.card ≤ K.edgeFinset.card) := by sorry
