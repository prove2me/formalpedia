-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- name    : WilliamsonShmoys.finite_planar_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:16:18.151698+00:00
-- url     : https://prove2.me/theorems/d28c47ee-1452-4cdd-bb6b-dd18e647b2d9
-- title:
--   Iterate finite edge augmentation to the bound
-- statement:
--   Given an edge bound and a drawable one-edge extension whenever a current supergraph is below that bound, finitely many extensions produce a drawable supergraph attaining the bound. This separates the elementary induction on the deficit from the planar topology.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (b : Nat) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hBound : ∀ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H → H.edgeSet.ncard ≤ b) (hStep : ∀ H : SimpleGraph V, G ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H.edgeSet.ncard < b → ∃ K : SimpleGraph V, H ≤ K ∧ K.edgeSet.ncard = H.edgeSet.ncard + 1 ∧ WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard = b := by sorry
