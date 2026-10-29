-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_face_incidence_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a4
-- name    : WilliamsonShmoys.finite_face_incidence_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:30:50.658909+00:00
-- url     : https://prove2.me/theorems/1e617845-84a7-4850-95b3-f3b95b3a1a08
-- title:
--   Count incidences in a triangular finite face system
-- statement:
--   For a finite edge set and a finite collection of triangular boundaries, if each boundary uses only designated edges and every designated edge occurs in exactly two boundaries, then counting face-edge incidences in the two orders gives three times the number of faces equal to twice the number of designated edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_face_incidence_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a4
    {E F : Type} [Fintype E] [Fintype F] [DecidableEq E]
    (edges : Set E) (boundary : F → Finset E)
    (hCard : ∀ f, (boundary f).card = 3)
    (hBoundary : ∀ f, ∀ e ∈ boundary f, e ∈ edges)
    (hIncidence : ∀ e ∈ edges,
      ((Finset.univ : Finset F).filter (fun f => e ∈ boundary f)).card = 2) :
    3 * Fintype.card F = 2 * edges.ncard := by sorry
