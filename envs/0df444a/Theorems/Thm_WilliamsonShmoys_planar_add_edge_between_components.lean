-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components
-- name    : WilliamsonShmoys.planar_add_edge_between_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:49:07.855452+00:00
-- url     : https://prove2.me/theorems/b3f9b640-d2aa-417b-942c-4505ce07564c
-- title:
--   Add an edge between distinct planar components
-- statement:
--   Given a finite planar graph and two vertices in distinct connected components, add an edge between those vertices while preserving a crossing-free drawing and strictly extending the edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_components
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (u v : V)
    (hreach : ¬ K.Reachable u v) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet ≠ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  sorry
