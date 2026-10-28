-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_face_data_arithmetic
-- name    : WilliamsonShmoys.planar_component_face_data_arithmetic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:14:32.793454+00:00
-- url     : https://prove2.me/theorems/dcad72ff-cbab-4dc8-872d-77cf98add119
-- title:
--   Sum component face data to obtain the planar edge bound
-- statement:
--   Given a disjoint nonempty partition, an edge-count sum, and the local face-count or small-size facts, derive the global planar edge bound. Convert each Euler/perimeter pair into the local bound `m ≤ 3n - 6`, then sum. A single block uses the global vertex lower bound; multiple blocks contribute at least six units of slack. The explicit `DecidableEq V` instance permits the induced edge-set counts in the statement; the parent supplies it from its linear order.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_face_data_arithmetic
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (parts : Finset (Finset V))
    (hV : 3 ≤ Fintype.card V)
    (hNonempty : ∀ C ∈ parts, C.Nonempty)
    (hDisjoint : ∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D)
    (hCover : parts.biUnion id = Finset.univ)
    (hEdgeSum : G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard)
    (hLocal : ∀ C ∈ parts,
      (G.induce (fun v => v ∈ C)).Connected ∧
      (if 3 ≤ C.card then
        ∃ f : ℕ,
          C.card + f = (G.induce (fun v => v ∈ C)).edgeSet.ncard + 2 ∧
          3 * f ≤ 2 * (G.induce (fun v => v ∈ C)).edgeSet.ncard
      else
        (G.induce (fun v => v ∈ C)).edgeSet.ncard ≤ 3 * C.card - 3)) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
