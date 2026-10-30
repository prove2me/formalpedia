-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion__p2m_3e20b199_32f9_4aa6_83e2_00145d2a7578_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_3e20b199_32f9_4aa6_83e2_00145d2a7578_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:13:55.877588+00:00
-- url     : https://prove2.me/theorems/49a7b880-a3f8-443f-bfbf-c306626f3a20
-- title:
--   Triangulated completion of a planar drawing
-- statement:
--   Any graph with a crossing-free drawing on a finite linearly ordered vertex type and at least three vertices is contained in a drawable supergraph on the same vertices whose edge count is `3|V|−6`. This isolates the topological completion and Euler-counting work from the parent’s short maximality argument. A proof route is to extend the drawing to a triangulation, handling disconnected drawings and nontriangular faces, and then count vertices, edges, and triangular faces using Euler’s formula. The claim covers the three-vertex boundary case, where completion yields the triangle; the formal proof must also establish that the completion preserves the exact arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_3e20b199_32f9_4aa6_83e2_00145d2a7578_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V, K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
