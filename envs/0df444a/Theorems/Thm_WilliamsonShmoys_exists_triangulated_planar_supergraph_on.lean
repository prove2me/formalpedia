-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_on
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph_on
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:14:03.90928+00:00
-- url     : https://prove2.me/theorems/bb901f48-5faf-4d4e-a4ac-9cdfd4c83114
-- title:
--   Planar triangulation extension on a fixed vertex set
-- statement:
--   Any graph with a supplied planar drawing on at least three finite ordered vertices has a planar supergraph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph_on
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKplanar : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
