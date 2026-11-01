-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_2a4e0817_5ede_4993_80da_c0938cce21b3_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_2a4e0817_5ede_4993_80da_c0938cce21b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:54:07.630061+00:00
-- url     : https://prove2.me/theorems/afb5df26-e4fb-4772-9aa3-0e4304c46b48
-- title:
--   Extend a planar graph to the maximal planar edge count
-- statement:
--   Every planar graph on a finite linearly ordered vertex type with at least three vertices has a planar supergraph on the same vertices with exactly 3n − 6 edges. The parent applies maximality to identify this supergraph with the original graph. The proposed proof route is to augment the drawing to a triangulated planar embedding and use Euler’s formula and the face-degree count. The child carries the remaining topological work; its statement is true at the boundary case n = 3, where the extension is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_2a4e0817_5ede_4993_80da_c0938cce21b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≤ M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
