-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_face_system_incidence_count
-- name    : WilliamsonShmoys.triangular_face_system_incidence_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:11:24.985727+00:00
-- url     : https://prove2.me/theorems/24f8e595-7427-4ae0-800b-8d7d21b265d8
-- title:
--   Count incidences in a triangular face system
-- statement:
--   For a finite simple graph, if every face occurrence contains three vertices, every pair of distinct vertices in a face is adjacent, and every graph edge occurs in exactly two faces, then counting face-edge incidences by faces and by edges gives three times the number of faces equal to twice the number of edges. The proof can count face occurrences together with unordered vertex pairs: each face contributes three pairs, while each graph edge contributes two face occurrences. This removes the combinatorial counting obligation from the parent; the parent combines the result with Euler’s equation using natural-number linear arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

theorem WilliamsonShmoys.triangular_face_system_incidence_count
    {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    (faces : Multiset (Finset V))
    (hcard : ∀ f, f ∈ faces → f.card = 3)
    (hadj : ∀ f, f ∈ faces → ∀ u, u ∈ f → ∀ v, v ∈ f → u ≠ v → H.Adj u v)
    (hedge : ∀ u v, H.Adj u v → (faces.filter (fun f => u ∈ f ∧ v ∈ f)).card = 2) :
    faces.card * 3 = H.edgeSet.ncard * 2 := by sorry
