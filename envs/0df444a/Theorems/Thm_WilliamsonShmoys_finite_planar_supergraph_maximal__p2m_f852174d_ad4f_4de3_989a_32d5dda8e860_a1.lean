-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
-- name    : WilliamsonShmoys.finite_planar_supergraph_maximal__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:56:17.392332+00:00
-- url     : https://prove2.me/theorems/302d93b5-7d6d-4d54-a31e-287e8e218082
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs containing it. No lower bound on the number of vertices is needed. The proof route is to maximize the edge count over the finite collection of drawable supergraphs containing K; inclusion into another such graph forces equality of edge counts and therefore equality of graphs. This removes the finite selection and maximality step from the parent. It does not address how many edges a maximal drawable graph has.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_planar_supergraph_maximal__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V, H ≤ J →
          WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by sorry
