-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_edge_card__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
-- name    : WilliamsonShmoys.planar_supergraph_max_edge_card__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:20.411926+00:00
-- url     : https://prove2.me/theorems/8f4450fd-25bb-4306-b9c5-7a9c9b261a7b
-- title:
--   A drawable supergraph maximizes edge cardinality
-- statement:
--   Among drawable supergraphs of a drawable graph on a finite vertex type, one has maximum edge cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_max_edge_card__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) : ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, N ≤ L → HasPlanarDrawingOn L → Nat.card {e : Sym2 V // e ∈ L.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ K.edgeSet} := by sorry
