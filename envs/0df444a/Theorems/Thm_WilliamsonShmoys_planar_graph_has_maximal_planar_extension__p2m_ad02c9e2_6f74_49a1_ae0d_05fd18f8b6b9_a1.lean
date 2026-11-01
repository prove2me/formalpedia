-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_extension__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
-- name    : WilliamsonShmoys.planar_graph_has_maximal_planar_extension__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:34.098885+00:00
-- url     : https://prove2.me/theorems/03bfe837-ddc7-49ff-ba57-41dcefd0c29f
-- title:
--   Every drawn finite graph has a maximal planar supergraph
-- statement:
--   Every finite graph with a crossing-free drawing is contained, on the same vertex set, in a graph with a crossing-free drawing that has no strictly larger planar supergraph on that vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_maximal_planar_extension__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
