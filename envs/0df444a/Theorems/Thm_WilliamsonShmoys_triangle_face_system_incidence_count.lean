-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangle_face_system_incidence_count
-- name    : WilliamsonShmoys.triangle_face_system_incidence_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:40:56.51023+00:00
-- url     : https://prove2.me/theorems/2e3e58b4-135f-418b-9f46-6ff6180fff66
-- title:
--   Count incidences in a triangular face system
-- statement:
--   For a multiset of three-vertex cliques in a finite simple graph, if every graph edge occurs in exactly two faces, then the total number of face-edge incidences counted by faces equals twice the number of graph edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.triangle_face_system_incidence_count
    {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    (faces : Multiset (Finset V))
    (hcard : ∀ f, f ∈ faces → f.card = 3)
    (hadj : ∀ f, f ∈ faces → ∀ u, u ∈ f → ∀ v, v ∈ f →
      u ≠ v → H.Adj u v)
    (hincidence : ∀ u v, H.Adj u v →
      (faces.filter (fun f => u ∈ f ∧ v ∈ f)).card = 2) :
    3 * faces.card = 2 * H.edgeSet.ncard := by
  sorry
