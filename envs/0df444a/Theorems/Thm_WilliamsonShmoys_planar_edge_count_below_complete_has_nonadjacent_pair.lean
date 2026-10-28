-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_below_complete_has_nonadjacent_pair
-- name    : WilliamsonShmoys.planar_edge_count_below_complete_has_nonadjacent_pair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:08:15.566804+00:00
-- url     : https://prove2.me/theorems/b99af42c-0bc8-4c54-92c7-5577fb1adc4c
-- title:
--   An edge bound below the planar maximum leaves a nonadjacent pair
-- statement:
--   For a finite simple graph with at least three vertices, fewer than 3|V|−6 edges implies that some distinct pair is nonadjacent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_below_complete_has_nonadjacent_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v := by sorry
