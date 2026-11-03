-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- name    : WilliamsonShmoys.planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:10:25.641902+00:00
-- url     : https://prove2.me/theorems/7d9aa82d-f2fe-4aa2-b79e-d2d48fb9feb3
-- title:
--   Connected planar supergraph
-- statement:
--   A graph with a planar drawing on a finite ordered vertex type of size at least three has a connected planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ C : SimpleGraph V,
      G ≤ C ∧ C.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn C := by sorry
