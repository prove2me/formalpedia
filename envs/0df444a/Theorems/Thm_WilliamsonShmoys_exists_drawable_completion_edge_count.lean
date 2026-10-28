-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_completion_edge_count
-- name    : WilliamsonShmoys.exists_drawable_completion_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:28:34.710316+00:00
-- url     : https://prove2.me/theorems/335ceae1-592f-4248-b5ff-6228c514ba74
-- title:
--   Drawable triangulated completion edge count
-- statement:
--   Every drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6. Construct a plane embedding from the supplied crossing-free arcs, connect components through faces, and add noncrossing edges until the faces are triangular; Euler's formula and face-degree counting yield the edge count. This child isolates the topological completion and counting work, leaving the parent to apply maximality and antisymmetry.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_completion_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
