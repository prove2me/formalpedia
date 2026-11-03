-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_extension__p2m_46bd3770_49b2_4c1a_90e5_69dd719cc31d_a1
-- name    : WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_46bd3770_49b2_4c1a_90e5_69dd719cc31d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:58:42.146183+00:00
-- url     : https://prove2.me/theorems/2932b977-69eb-43f4-aaa9-a9ebd474ac36
-- title:
--   A disconnected planar drawing admits an edge extension
-- statement:
--   For a drawable graph on at least three finite linearly ordered vertices, if the graph is disconnected, there are distinct nonadjacent vertices that can be joined by an edge so that the resulting supergraph is still drawable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_46bd3770_49b2_4c1a_90e5_69dd719cc31d_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) [DecidableRel K.Adj] (hcard : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hconn : ¬ K.Connected) : ∃ x y : V, ∃ L : SimpleGraph V, x ≠ y ∧ ¬ K.Adj x y ∧ K ≤ L ∧ L.Adj x y ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
