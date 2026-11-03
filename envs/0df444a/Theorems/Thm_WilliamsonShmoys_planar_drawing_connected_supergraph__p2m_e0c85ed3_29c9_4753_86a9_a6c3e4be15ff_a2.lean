-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:26.133521+00:00
-- url     : https://prove2.me/theorems/9e44a517-8676-4467-979c-aa3ee27ed644
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   A finite nonempty graph with a crossing-free drawing can be extended, on the same vertex set, to a connected graph that contains all its original edges and still has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 0 < Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
