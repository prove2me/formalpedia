-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_has_nonadjacent_pair
-- name    : WilliamsonShmoys.planar_drawing_disconnected_has_nonadjacent_pair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:07:47.003232+00:00
-- url     : https://prove2.me/theorems/1a540270-931f-4b19-b45d-d1dc41aa1c98
-- title:
--   Disconnected finite graph has a separated nonadjacent pair
-- statement:
--   A disconnected finite graph with at least three vertices has distinct vertices in different connected components; such vertices are not adjacent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_disconnected_has_nonadjacent_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ H.Reachable u v ∧ ¬ H.Adj u v := by
  sorry
