-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_property_supergraph__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
-- name    : WilliamsonShmoys.finite_maximal_property_supergraph__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:37:26.947015+00:00
-- url     : https://prove2.me/theorems/94840855-3f80-4ebf-bea7-e02128c254e5
-- title:
--   A downward-closed property has a maximal graph extension on a finite vertex type
-- statement:
--   For a finite vertex type, every nonempty property of simple graphs that is preserved when edges are removed has a graph that is maximal under inclusion among graphs satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.finite_maximal_property_supergraph__p2m_73c85c29_4333_4692_baee_7210fe30cead_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G)
    (hP : ∃ G : SimpleGraph V, P G) :
    ∃ N : SimpleGraph V,
      P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by sorry
