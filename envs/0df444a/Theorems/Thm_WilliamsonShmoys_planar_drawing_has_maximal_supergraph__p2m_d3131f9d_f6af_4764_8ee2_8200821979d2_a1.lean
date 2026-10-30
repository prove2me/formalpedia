-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:21.823007+00:00
-- url     : https://prove2.me/theorems/2146180a-8ed0-4c7d-8037-73a13382ac2a
-- title:
--   A planar drawing has a maximal planar supergraph
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex set that is maximal under subgraph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ G : SimpleGraph V,
          H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G = H := by
  sorry
