-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_spanning_supergraph_of_at_least_three_vertices
-- name    : WilliamsonShmoys.planar_connected_spanning_supergraph_of_at_least_three_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:48:10.958267+00:00
-- url     : https://prove2.me/theorems/1d4beccf-a492-4c0d-bd7a-352b7e8f65ab
-- title:
--   Connected planar spanning supergraph with at least three vertices
-- statement:
--   A finite graph with at least three vertices and a crossing-free drawing has a connected planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_spanning_supergraph_of_at_least_three_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
