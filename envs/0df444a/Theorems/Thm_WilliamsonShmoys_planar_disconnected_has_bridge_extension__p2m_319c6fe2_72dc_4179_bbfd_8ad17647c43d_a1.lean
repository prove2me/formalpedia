-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_bridge_extension__p2m_319c6fe2_72dc_4179_bbfd_8ad17647c43d_a1
-- name    : WilliamsonShmoys.planar_disconnected_has_bridge_extension__p2m_319c6fe2_72dc_4179_bbfd_8ad17647c43d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:39.325239+00:00
-- url     : https://prove2.me/theorems/cb139db2-73c1-451e-b6a9-3cccdec58a46
-- title:
--   Planar extension with an explicit new bridge edge
-- statement:
--   For a disconnected drawable graph on at least three vertices, there is a planar supergraph containing an edge whose endpoints were not adjacent in the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_has_bridge_extension__p2m_319c6fe2_72dc_4179_bbfd_8ad17647c43d_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hdisc : ¬ H.Connected) :
    ∃ u v : V, ∃ G : SimpleGraph V,
      ¬ H.Adj u v ∧ H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Adj u v := by
  sorry
