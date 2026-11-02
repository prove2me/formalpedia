-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:36:27.070075+00:00
-- url     : https://prove2.me/theorems/184d0625-bb96-4aaf-8936-3881fc188830
-- title:
--   Finite maximal planar extension
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that is maximal among planar supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
        ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
