-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_card_sym2
-- name    : WilliamsonShmoys.edgeSet_ncard_le_card_sym2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:38:05.990339+00:00
-- url     : https://prove2.me/theorems/2c00d713-73cd-4f1b-8fdc-3426a422fa0c
-- title:
--   A finite graph’s edge count is bounded by its edge universe
-- statement:
--   For a finite vertex type, a simple graph’s edge count is at most the number of possible unordered vertex pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_le_card_sym2 {V : Type} [Fintype V] (G : SimpleGraph V) : G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by sorry
