-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_induce
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_induce
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:18:23.736732+00:00
-- url     : https://prove2.me/theorems/3ab9e828-4297-49a9-9429-7656743a1384
-- title:
--   Induced subgraphs inherit planar drawings
-- statement:
--   Restricting a crossing-free drawing to a finite subset of vertices gives a crossing-free drawing of the induced subgraph. The explicit finite instance supports the subtype cardinality and induced graph in the statement; in the parent, classical inference supplies it because the ambient vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_induce
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (S : Set V) [Fintype S] :
    WilliamsonShmoys.HasPlanarDrawingOn (K.induce S) := by sorry
