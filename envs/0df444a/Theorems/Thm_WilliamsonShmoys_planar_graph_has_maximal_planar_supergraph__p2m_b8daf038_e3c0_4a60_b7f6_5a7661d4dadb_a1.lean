-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_supergraph__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
-- name    : WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:26:18.786654+00:00
-- url     : https://prove2.me/theorems/e07f1b1a-1ea6-4563-8b26-8f130e22d586
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph that is maximal under inclusion among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry
