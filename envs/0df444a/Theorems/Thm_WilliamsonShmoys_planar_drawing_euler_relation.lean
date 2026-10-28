-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_relation
-- name    : WilliamsonShmoys.planar_drawing_euler_relation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:13:55.009993+00:00
-- url     : https://prove2.me/theorems/7df73744-3ada-4f2e-9aa8-f35a174e70a1
-- title:
--   Euler relation for a planar drawing
-- statement:
--   A finite graph with at least three vertices and a crossing-free drawing has a natural face count and component count satisfying Euler’s relation, with at least one component. The component count includes isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_relation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ (f c : ℕ),
      Fintype.card V + f = L.edgeSet.ncard + c + 1 ∧
      1 ≤ c := by sorry
