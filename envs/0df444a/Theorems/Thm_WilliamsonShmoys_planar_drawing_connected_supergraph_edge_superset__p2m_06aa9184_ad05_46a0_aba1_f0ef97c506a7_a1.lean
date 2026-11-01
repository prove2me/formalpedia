-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_edge_superset__p2m_06aa9184_ad05_46a0_aba1_f0ef97c506a7_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_edge_superset__p2m_06aa9184_ad05_46a0_aba1_f0ef97c506a7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:51:42.024539+00:00
-- url     : https://prove2.me/theorems/e072abf9-a18d-4ec4-b40d-84b33bde54a7
-- title:
--   Connected planar supergraph preserving the original edges
-- statement:
--   Every finite planar drawing on a vertex type with at least three vertices can be extended to a connected planar graph on the same vertex type while retaining all original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_edge_superset__p2m_06aa9184_ad05_46a0_aba1_f0ef97c506a7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧ M ≤ H := by
  sorry
