-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_face_data_of_local_edge_bounds
-- name    : WilliamsonShmoys.planar_drawing_component_face_data_of_local_edge_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:25:59.507198+00:00
-- url     : https://prove2.me/theorems/282c3624-60d5-414b-afb0-802911ee935a
-- title:
--   Assemble component face data from local edge bounds
-- statement:
--   Given a finite simple graph and an upper edge bound for every connected induced subset of size at least three, partition the vertices into nonempty connected blocks, decompose the total edge count across the blocks, and supply the requested face-count data or small-size edge bound for every block.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_component_face_data_of_local_edge_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hlocal : ∀ C : Finset V, C.Nonempty →
      (G.induce (fun v => v ∈ C)).Connected →
      3 ≤ C.card →
      (G.induce (fun v => v ∈ C)).edgeSet.ncard + 6 ≤ 3 * C.card) :
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
