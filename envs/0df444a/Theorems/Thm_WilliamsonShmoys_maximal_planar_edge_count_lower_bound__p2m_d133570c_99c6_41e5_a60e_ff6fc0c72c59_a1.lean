-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:00:03.51579+00:00
-- url     : https://prove2.me/theorems/300e589a-9958-4177-9a18-5a010b7286b4
-- title:
--   Maximality forces the planar lower bound
-- statement:
--   A drawable graph on at least three finite vertices that has no drawable proper supergraph has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M → M ≤ K) :
    (letI : DecidableRel K.Adj := dK;
      3 * Fintype.card V - 6 ≤ K.edgeFinset.card) := by sorry
