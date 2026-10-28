-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_spanning_augmentation
-- name    : WilliamsonShmoys.planar_drawing_connected_spanning_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:58:39.125191+00:00
-- url     : https://prove2.me/theorems/468dfd4c-ca00-435a-b628-f50b25f40cec
-- title:
--   Connected spanning augmentation of a planar drawing
-- statement:
--   A graph on at least three vertices with the specified crossing-free drawing has a connected spanning supergraph with a crossing-free drawing on the same vertex type. Connectivity is expressed as reflexive-transitive reachability along graph adjacency.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_spanning_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J ≤ K ∧
      (∀ u v, Relation.ReflTransGen K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
