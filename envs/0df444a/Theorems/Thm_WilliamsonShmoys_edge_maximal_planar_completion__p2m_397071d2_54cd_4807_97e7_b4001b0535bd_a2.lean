-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_completion__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
-- name    : WilliamsonShmoys.edge_maximal_planar_completion__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:24:12.278846+00:00
-- url     : https://prove2.me/theorems/73e7b93f-69a7-40ff-8c86-d281f4aa9073
-- title:
--   Finite edge-maximal planar completion
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs. This isolates the finite maximization step and asserts no edge count. A proof can maximize the edge-set cardinality over the finite set of candidate simple graphs, then use inclusion and cardinality to establish maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_completion__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) := by
  sorry
