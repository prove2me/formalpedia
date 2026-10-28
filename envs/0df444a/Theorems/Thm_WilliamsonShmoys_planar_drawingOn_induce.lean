-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_induce
-- name    : WilliamsonShmoys.planar_drawingOn_induce
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:58:25.275215+00:00
-- url     : https://prove2.me/theorems/d6958d3b-2ae9-4bc8-9345-2b4e8459bd7d
-- title:
--   Restrict a planar drawing to an induced vertex subset
-- statement:
--   Restrict the injective vertex placement and the edge arcs in the supplied drawing to the subtype of vertices in S. This removes the drawing-restriction step from the parent proof. A direct proof unpacks HasPlanarDrawingOn, composes the placement and arcs with the subtype coercion, and uses the induced graph’s adjacency definition. The linear order on the subtype agrees with the ambient order, so the orientation conditions on each edge are preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_induce
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (S : Finset V) :
    HasPlanarDrawingOn (K.induce (↑S : Set V)) := by sorry
