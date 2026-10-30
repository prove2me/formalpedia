-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_3b82d126
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3b82d126
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:36:47.03998+00:00
-- url     : https://prove2.me/theorems/60c881fb-af42-4cde-9ce2-9b447690b4d8
-- title:
--   Edge-count lower bound from maximality
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex set, with at least three vertices, has at least \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3b82d126
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      ∀ ⦃u v⦄, M.Adj u v → K.Adj u v) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
