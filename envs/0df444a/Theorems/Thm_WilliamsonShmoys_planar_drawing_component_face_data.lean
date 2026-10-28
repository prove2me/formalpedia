-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_face_data
-- name    : WilliamsonShmoys.planar_drawing_component_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:10:52.737912+00:00
-- url     : https://prove2.me/theorems/b44779b8-e753-4bde-89ec-ab0c26e36ea8
-- title:
--   Component face counts from a planar drawing
-- statement:
--   Partition the vertices into nonempty, disjoint blocks whose induced graphs are connected, decompose the edge count across the blocks, and give each block either a direct small-size edge bound or Euler and perimeter data for its face count. Prove this by taking graph components, restricting the drawing to each induced component, and establishing Euler’s formula and the edge-side count for the resulting connected planar embedding. The cases of one or two vertices use simplicity directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_component_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard ∧
      (∀ C ∈ parts,
        (G.induce (fun v => v ∈ C)).Connected ∧
        (if 3 ≤ C.card then
          ∃ f : ℕ,
            C.card + f = (G.induce (fun v => v ∈ C)).edgeSet.ncard + 2 ∧
            3 * f ≤ 2 * (G.induce (fun v => v ∈ C)).edgeSet.ncard
        else
          (G.induce (fun v => v ∈ C)).edgeSet.ncard ≤ 3 * C.card - 3)) := by sorry
