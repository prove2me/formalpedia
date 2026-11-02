-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2932b977_69eb_43f4_aaa9_a9ebd474ac36_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_2932b977_69eb_43f4_aaa9_a9ebd474ac36_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:55:22.881302+00:00
-- url     : https://prove2.me/theorems/6d69b60d-131c-43ed-9c9d-8adf863c3ac3
-- title:
--   Connected planar extension on the same vertex set
-- statement:
--   A graph with a crossing-free drawing on at least three finite ordered vertices has a connected supergraph on the same vertices that still has such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_2932b977_69eb_43f4_aaa9_a9ebd474ac36_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) [DecidableRel K.Adj] (hcard : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ L.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
