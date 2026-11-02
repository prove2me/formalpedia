-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T07:01:57.167129+00:00
-- url     : https://prove2.me/theorems/986cca2a-af96-41ca-97f1-9fc97c42977c
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Any finite graph with a crossing-free drawing can be extended, on the same vertex set, to a connected graph with a crossing-free drawing and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun (H : SimpleGraph V) =>
      Exists fun (dH : DecidableRel H.Adj) =>
        And H.Connected
          (And (WilliamsonShmoys.HasPlanarDrawingOn H)
            (Nat.le K.edgeFinset.card H.edgeFinset.card)) := by
  sorry
