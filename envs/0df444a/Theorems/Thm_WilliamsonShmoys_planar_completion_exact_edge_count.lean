-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count
-- name    : WilliamsonShmoys.planar_completion_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:22:23.469993+00:00
-- url     : https://prove2.me/theorems/bcd4e9c3-c6c5-4ab9-a677-a426a2d621a7
-- title:
--   Sparse drawable graphs have a maximal planar completion
-- statement:
--   A drawable simple graph on at least three vertices with fewer than 3|V|−6 edges has a drawable supergraph on the same vertices with exactly 3|V|−6 edges, and that supergraph strictly adds edges. The strict inequality is necessary: the conclusion is not asserted at the maximal planar edge-count boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      ¬ K.edgeSet ⊆ H.edgeSet := by sorry
