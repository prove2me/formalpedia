-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_ca4f62b0_0fc3_4b70_a0ef_3ca6355feff9_a1
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_ca4f62b0_0fc3_4b70_a0ef_3ca6355feff9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:25:34.834165+00:00
-- url     : https://prove2.me/theorems/a3e0b5a8-b607-4050-8296-f0effeafa525
-- title:
--   Euler and triangular-face equations for a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set admits a face count satisfying Euler's equation and the triangular face-edge incidence equation. Together, these equations give the required edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_ca4f62b0_0fc3_4b70_a0ef_3ca6355feff9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
