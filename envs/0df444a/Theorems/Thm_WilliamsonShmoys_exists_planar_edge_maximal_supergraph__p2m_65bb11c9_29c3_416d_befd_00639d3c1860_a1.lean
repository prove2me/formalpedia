-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_maximal_supergraph__p2m_65bb11c9_29c3_416d_befd_00639d3c1860_a1
-- name    : WilliamsonShmoys.exists_planar_edge_maximal_supergraph__p2m_65bb11c9_29c3_416d_befd_00639d3c1860_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:22.270351+00:00
-- url     : https://prove2.me/theorems/8945f9a8-f1f1-4069-b3b7-48c3e7c6f526
-- title:
--   Finite maximal planar supergraph exists
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_edge_maximal_supergraph__p2m_65bb11c9_29c3_416d_befd_00639d3c1860_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    [DecidableRel P.Adj] :
    ∃ H : SimpleGraph V,
      P ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H) := by sorry
