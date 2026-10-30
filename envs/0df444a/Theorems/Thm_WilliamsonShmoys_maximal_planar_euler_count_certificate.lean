-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count_certificate
-- name    : WilliamsonShmoys.maximal_planar_euler_count_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:02:47.907392+00:00
-- url     : https://prove2.me/theorems/ed91fffc-a32b-46e0-9209-f57c29a4258c
-- title:
--   Euler and triangular-face count for a maximal planar drawing
-- statement:
--   A drawable graph that is inclusion-maximal among drawable supergraphs on the same vertices has a face count satisfying both the plane Euler equation and the triangular-face edge-incidence equation. The proof route is to derive a plane embedding from the arc drawing, show maximality forces connectedness and triangular faces, and count incidences. These two equations remove the final arithmetic from the parent; deriving them from the drawing and maximality is the remaining core geometric work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.maximal_planar_euler_count_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall K : SimpleGraph V, M <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    exists f : Nat,
      (Fintype.card V : Int) - (M.edgeSet.ncard : Int) + (f : Int) = 2 /\
      (3 : Int) * (f : Int) = 2 * (M.edgeSet.ncard : Int) := by sorry
