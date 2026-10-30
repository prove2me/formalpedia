-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_edge_card_le__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
-- name    : WilliamsonShmoys.simpleGraph_eq_of_edge_card_le__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:18.650836+00:00
-- url     : https://prove2.me/theorems/7e84bdd8-e4c0-465d-9cd8-75effca7566a
-- title:
--   Inclusion and edge cardinalities determine graph equality
-- statement:
--   For finite simple graphs, inclusion and the reverse edge cardinality inequality imply equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_eq_of_edge_card_le__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2 {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) (hcard : Nat.card {e : Sym2 V // e ∈ H.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ G.edgeSet}) : H = G := by sorry
