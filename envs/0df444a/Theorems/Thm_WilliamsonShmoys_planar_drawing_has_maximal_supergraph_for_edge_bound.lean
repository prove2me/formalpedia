-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:31:31.770613+00:00
-- url     : https://prove2.me/theorems/8a3d48ef-a7ea-4ba8-ac0d-40a593dbe7d8
-- title:
--   A drawn planar graph has a maximal drawn supergraph
-- statement:
--   Every finite graph with a drawing has a drawn supergraph on the same vertices that is maximal under edge inclusion. The finiteness of the possible simple graphs permits choosing one with maximal edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      ∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L →
        H.edgeSet ⊆ L.edgeSet →
        L.edgeSet ⊆ H.edgeSet := by sorry
