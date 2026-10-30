-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_23bdb811_aa64_4006_9931_e87966df2d08_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_23bdb811_aa64_4006_9931_e87966df2d08_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:36:05.410557+00:00
-- url     : https://prove2.me/theorems/4b265a90-b8bd-4522-9040-b7d7632358e1
-- title:
--   Triangulated planar supergraph on the same vertices
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_23bdb811_aa64_4006_9931_e87966df2d08_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
