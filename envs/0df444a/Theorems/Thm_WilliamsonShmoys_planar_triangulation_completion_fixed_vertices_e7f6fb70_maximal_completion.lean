-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_completion
-- name    : WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:46:20.624712+00:00
-- url     : https://prove2.me/theorems/a8a2b015-4671-4c4e-98b7-a2dbf4c0a0b4
-- title:
--   Maximal drawable completion on a fixed vertex type
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    Exists fun Y : SimpleGraph V =>
      X <= Y /\ WilliamsonShmoys.HasPlanarDrawingOn Y /\
      (forall Z : SimpleGraph V, Y <= Z ->
        WilliamsonShmoys.HasPlanarDrawingOn Z -> Z = Y) := by sorry
