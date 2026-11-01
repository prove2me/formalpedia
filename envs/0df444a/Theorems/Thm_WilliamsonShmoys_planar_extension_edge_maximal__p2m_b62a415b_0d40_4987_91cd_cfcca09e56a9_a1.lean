-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_edge_maximal__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
-- name    : WilliamsonShmoys.planar_extension_edge_maximal__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:50.337104+00:00
-- url     : https://prove2.me/theorems/43c67fa9-4f37-4b3c-a62f-58a2e3b2eb90
-- title:
--   Finite maximal drawable extension
-- statement:
--   Any drawable graph on a finite linearly ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_edge_maximal__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V) (hdec : DecidableRel H.Adj),
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeFinset.card ≤ H.edgeFinset.card ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  sorry
