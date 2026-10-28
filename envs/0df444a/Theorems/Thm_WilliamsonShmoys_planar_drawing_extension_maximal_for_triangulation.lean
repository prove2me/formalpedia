-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_maximal_for_triangulation
-- name    : WilliamsonShmoys.planar_drawing_extension_maximal_for_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:38:43.30276+00:00
-- url     : https://prove2.me/theorems/10281626-7c2c-4e2e-b301-3eb05768025b
-- title:
--   Maximal planar drawing extension for triangulation
-- statement:
--   Every finite graph with a crossing-free drawing has a crossing-free supergraph on the same vertices that is maximal among crossing-free supergraphs. This removes the finite maximization argument from the parent proof; prove it by maximizing edge-set cardinality among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extension_maximal_for_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      P.edgeSet ⊆ Q.edgeSet ∧
      (∀ R : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn R →
        Q.edgeSet ⊆ R.edgeSet → R.edgeSet ⊆ Q.edgeSet) := by sorry
