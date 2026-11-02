-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_on_same_vertices__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1
-- name    : WilliamsonShmoys_maximal_planar_extension_on_same_vertices__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:01.035909+00:00
-- url     : https://prove2.me/theorems/0ddd1fcd-d7d5-4187-a3cf-073eb037e06a
-- title:
--   Extend a connected planar graph to a maximal planar supergraph
-- statement:
--   A connected graph with at least three vertices and a drawing satisfying the packaged planar-drawing predicate has a planar supergraph on the same vertices that is inclusion-maximal among simple planar supergraphs. Its edge count is at least that of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_extension_on_same_vertices__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      K.edgeSet.ncard ≤ L.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
