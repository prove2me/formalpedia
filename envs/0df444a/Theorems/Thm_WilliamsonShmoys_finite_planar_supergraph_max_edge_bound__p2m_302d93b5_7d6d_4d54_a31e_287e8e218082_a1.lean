-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_max_edge_bound__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
-- name    : WilliamsonShmoys.finite_planar_supergraph_max_edge_bound__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:42.471534+00:00
-- url     : https://prove2.me/theorems/069ee0fb-cc74-4f1e-9e46-922759cda9e8
-- title:
--   A drawable supergraph of maximum edge count
-- statement:
--   Among the drawable supergraphs of K on the finite vertex type V, there is one whose edge set has maximum finite cardinality. The family is nonempty since K belongs to it. This isolates the finite selection and maximization step from the target. It remains valid for V empty; the proof route is to use the finite type of graphs on V and maximize `edgeSet.ncard` over the nonempty subtype satisfying the two predicates.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_supergraph_max_edge_bound__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V, K ≤ J → HasPlanarDrawingOn J →
          J.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
