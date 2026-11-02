-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:22:59.162656+00:00
-- url     : https://prove2.me/theorems/88ecff63-43e7-40a6-a43a-e55e1d9660ef
-- title:
--   Maximal planar extension on a fixed vertex set
-- statement:
--   Every graph with the given planar drawing is contained in an edge-maximal planar graph on the same finite vertex type. The maximality condition says that any planar supergraph on that type has the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by sorry
