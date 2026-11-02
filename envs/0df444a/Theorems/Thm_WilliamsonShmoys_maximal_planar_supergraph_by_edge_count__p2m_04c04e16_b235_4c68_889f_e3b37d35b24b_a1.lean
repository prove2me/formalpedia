-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_by_edge_count__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_by_edge_count__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:44.509809+00:00
-- url     : https://prove2.me/theorems/6f01502d-1270-4c66-a172-91bff8a4f944
-- title:
--   Maximum-edge drawable supergraph exists
-- statement:
--   Among the drawable supergraphs of a finite drawable graph on the same vertex type, there is one whose edge count is at least that of every other drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_by_edge_count__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V),
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V),
        (∀ ⦃u v : V⦄, H.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeSet.ncard ≥ L.edgeSet.ncard) := by sorry
