-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:48:52.548199+00:00
-- url     : https://prove2.me/theorems/8e16201b-1194-4bde-8c0d-f203800a8dc6
-- title:
--   Connect a finite planar drawing with at least three vertices
-- statement:
--   A finite simple graph on at least three vertices with the given crossing-free drawing can be extended on the same vertex set to a connected graph with a crossing-free drawing and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : Nat.le 3 (Fintype.card V)) :
    Exists fun (H : SimpleGraph V) =>
      Exists fun (dH : DecidableRel H.Adj) =>
        And H.Connected
          (And (WilliamsonShmoys.HasPlanarDrawingOn H)
            (Nat.le K.edgeFinset.card H.edgeFinset.card)) := by
  sorry
