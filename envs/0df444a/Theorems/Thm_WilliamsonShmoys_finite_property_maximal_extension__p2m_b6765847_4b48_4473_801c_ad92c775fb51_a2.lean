-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_property_maximal_extension__p2m_b6765847_4b48_4473_801c_ad92c775fb51_a2
-- name    : WilliamsonShmoys.finite_property_maximal_extension__p2m_b6765847_4b48_4473_801c_ad92c775fb51_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:02:47.378763+00:00
-- url     : https://prove2.me/theorems/e7690aee-1ec6-4eed-8865-997ffa4c6ecd
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For any property of graphs on a finite vertex type, a graph satisfying the property has a supergraph satisfying it that has at least as many edges and admits no larger supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_property_maximal_extension__p2m_b6765847_4b48_4473_801c_ad92c775fb51_a2
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (N : SimpleGraph V)
    (hN : P N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧
      P H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V,
        H ≤ K → P K → K ≤ H) := by sorry
