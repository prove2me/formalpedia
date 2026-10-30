-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
-- name    : WilliamsonShmoys.maximal_planar_edge_count_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:09:56.10498+00:00
-- url     : https://prove2.me/theorems/a011dfae-6bb1-4297-ac30-fa674e714593
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertex type has at most three times the number of vertices minus six edges. This removes the planar counting obligation from the parent; the proof must establish the structural consequences of maximality and apply Euler’s formula with the face-boundary count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
