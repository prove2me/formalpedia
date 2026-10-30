-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_card_property__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a4
-- name    : WilliamsonShmoys.planar_supergraph_max_card_property__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:04.65896+00:00
-- url     : https://prove2.me/theorems/056354fe-8081-4e5e-ae62-0d709f8aad22
-- title:
--   Maximum-cardinality planar supergraph and equal-cardinality rigidity
-- statement:
--   There is a planar supergraph of `J` with maximum ordered-adjacency cardinality among planar extensions. For any planar extension of that graph, its adjacency cardinality is no larger; if the cardinalities are equal, inclusion forces the graphs to be equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_max_card_property__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a4 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → (Nat.card {p : V × V // L.Adj p.1 p.2} ≤ Nat.card {p : V × V // K.Adj p.1 p.2}) ∧ (Nat.card {p : V × V // L.Adj p.1 p.2} = Nat.card {p : V × V // K.Adj p.1 p.2} → L ≤ K) := by sorry
