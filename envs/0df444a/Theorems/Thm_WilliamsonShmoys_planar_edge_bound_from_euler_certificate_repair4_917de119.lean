-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_euler_certificate_repair4_917de119
-- name    : WilliamsonShmoys.planar_edge_bound_from_euler_certificate_repair4_917de119
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:47:24.996956+00:00
-- url     : https://prove2.me/theorems/77e6b04e-6074-436d-b1ed-6aaccca4f13a
-- title:
--   Planar edge bound from face counts
-- statement:
--   Derive the simple planar edge bound from the minimum face-boundary lengths, the twice-counted edge incidence sum, and Euler’s equation. An independent proof sums the face inequalities and rearranges the resulting natural-number equalities and inequalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_euler_certificate_repair4_917de119
    {V F : Type} [Fintype V] [Fintype F]
    (G : SimpleGraph V)
    (boundaryLength : F → ℕ)
    (hFace : ∀ f : F, 3 <= boundaryLength f)
    (hIncidence : Finset.sum Finset.univ boundaryLength = 2 * G.edgeSet.ncard)
    (hEuler : Fintype.card V + Fintype.card F = G.edgeSet.ncard + 2) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
