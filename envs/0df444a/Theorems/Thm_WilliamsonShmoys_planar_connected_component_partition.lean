-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_component_partition
-- name    : WilliamsonShmoys.planar_connected_component_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:24:23.041502+00:00
-- url     : https://prove2.me/theorems/d78b1ed6-5418-4c65-a391-1617d95f69be
-- title:
--   Partition a planar drawing into connected components
-- statement:
--   Extract the finite connected components as a vertex partition, show each edge has both endpoints in one part, and restrict the given drawing to each induced component. The empty graph has the empty partition; every listed part is nonempty. This isolates the finite graph-component and drawing-restriction work from the edge-count argument. A proof route is to use the connected-component equivalence relation, take its finite equivalence classes, and restrict the vertex-location and arc functions to each class.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_component_partition
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ C : Finset (Finset V),
      (∀ S ∈ C, S.Nonempty) ∧
      (∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S) ∧
      (∀ ⦃u v : V⦄, H.Adj u v → ∃ S ∈ C, u ∈ S ∧ v ∈ S) ∧
      (∀ S ∈ C, (H.induce (↑S : Set V)).Connected) ∧
      (∀ S ∈ C, WilliamsonShmoys.HasPlanarDrawingOn
        (H.induce (↑S : Set V))) := by sorry
