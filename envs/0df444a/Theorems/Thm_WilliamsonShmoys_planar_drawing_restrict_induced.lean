-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_restrict_induced
-- name    : WilliamsonShmoys.planar_drawing_restrict_induced
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:53:00.475892+00:00
-- url     : https://prove2.me/theorems/3db6ec00-b2e3-4093-a12f-102bebf1bed5
-- title:
--   Restrict a planar drawing to an induced subgraph
-- statement:
--   For a vertex subset equipped with an explicit finite instance, the original drawing restricts to a crossing-free drawing of the induced subgraph. The explicit instance handles arbitrary sets whose membership predicate does not provide decidable finite enumeration automatically.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_restrict_induced
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (W : Set V) (hFW : Fintype W) :
    WilliamsonShmoys.HasPlanarDrawingOn (K.induce W) := by sorry
