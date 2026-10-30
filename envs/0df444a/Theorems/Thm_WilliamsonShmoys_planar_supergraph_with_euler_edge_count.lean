-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_with_euler_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:11:01.178988+00:00
-- url     : https://prove2.me/theorems/b144c282-bd51-48dd-8966-bc3e54818cc5
-- title:
--   Planar supergraph with Euler edge count
-- statement:
--   Any graph with a crossing-free drawing on a finite ordered vertex type with at least three vertices has a planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_with_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
