-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:36.64052+00:00
-- url     : https://prove2.me/theorems/1cfa7f7c-e9eb-4312-90c1-05b7f255b2ad
-- title:
--   Maximal planar graphs attain the planar edge bound
-- statement:
--   A graph with a crossing-free drawing that is inclusion-maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3n − 6 edges. Together with the planar upper bound, this gives the target equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V,
      (∀ u v, P.Adj u v → Q.Adj u v) →
      HasPlanarDrawingOn Q →
      (∀ u v, Q.Adj u v → P.Adj u v)) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by
  sorry
