-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_max_card__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a3
-- name    : WilliamsonShmoys.planar_supergraph_max_card__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:55:51.206147+00:00
-- url     : https://prove2.me/theorems/57d36944-770c-4d46-99be-52926779c9ff
-- title:
--   Finite maximum-cardinality planar supergraph
-- statement:
--   Among planar supergraphs of `J`, choose one with maximum cardinality of its ordered adjacent-pair subtype. Any planar extension not contained in it has strictly more ordered adjacent pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_max_card__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a3 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → ¬ L ≤ K → Nat.card {p : V × V // K.Adj p.1 p.2} < Nat.card {p : V × V // L.Adj p.1 p.2} := by sorry
